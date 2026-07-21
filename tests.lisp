(defpackage #:lp-hash-table/test
  (:use #:cl #:lp-hash-table #:fiveam)
  (:export #:all #:run-tests))
(in-package #:lp-hash-table/test)

(def-suite all :description "lp-hash-table correctness")
(in-suite all)

(defun run-tests () (run! 'all))

;; A sensible fixnum hash (multiplicative; well-distributed low+high bits), like
;; the benchmark's -- SXHASH on fixnums is not what we use in practice.
(declaim (inline fxhash))
(defun fxhash (x)
  (declare (type fixnum x))
  (logand (* (logand x #x3fffffff) 2654435769) most-positive-fixnum))

(define-hash-set   fixnum-set fxhash eq)
(define-hash-table str-table (lambda (s) (sxhash (the string s))) equal)
(define-hash-table str-table-sh (lambda (s) (sxhash (the string s))) equal :store-hash t)

(test basic-set
  (let ((s (make-fixnum-set)))
    (is (null (nth-value 1 (fixnum-set-get 5 s))) "absent before put")
    (is (eql 5 (fixnum-set-put 5 s)))
    (multiple-value-bind (v p) (fixnum-set-get 5 s)
      (is (eql 5 v)) (is-true p))
    (is (= 1 (fixnum-set-count s)))
    (is (eql 5 (fixnum-set-put 5 s)) "intern returns existing")
    (is (= 1 (fixnum-set-count s)) "intern does not grow count")
    (is-true (fixnum-set-rem 5 s))
    (is (null (nth-value 1 (fixnum-set-get 5 s))))
    (is (= 0 (fixnum-set-count s)))
    (is (null (fixnum-set-rem 5 s)) "rem of absent")))

(test basic-table
  (let ((h (make-str-table)))
    (is (eql 42 (str-table-put "a" 42 h)))
    (is (eql 42 (str-table-get "a" h)))
    (is (eql 99 (str-table-put "a" 99 h)) "update returns new value")
    (is (eql 99 (str-table-get "a" h)))
    (is (= 1 (str-table-count h)))
    (is (eq :none (str-table-get "b" h :none)) "default on miss")
    (is-true (str-table-rem "a" h))
    (is (= 0 (str-table-count h)))))

(test intern-distinct-but-equal-keys
  (let ((h (make-str-table)))
    (str-table-put (copy-seq "key") 1 h)
    (is (= 1 (str-table-count h)))
    (is (eql 1 (str-table-get (copy-seq "key") h)) "found via distinct equal key")
    (str-table-put (copy-seq "key") 2 h)
    (is (= 1 (str-table-count h)) "distinct equal key updates, not inserts")
    (is (eql 2 (str-table-get "key" h)))))

(test insertion-order
  (let ((s (make-fixnum-set)) (got '()))
    (dotimes (i 200) (fixnum-set-put (* i 7) s))
    (map-fixnum-set (lambda (k) (push k got)) s)
    (is (equal (nreverse got) (loop for i below 200 collect (* i 7)))
        "MAP- iterates in insertion order")))

(test table-map-pairs
  (let ((h (make-str-table)) (sum 0) (n 0))
    (dotimes (i 100) (str-table-put (format nil "k~a" i) i h))
    (map-str-table (lambda (k v) (declare (ignore k)) (incf n) (incf sum v)) h)
    (is (= n 100))
    (is (= sum (loop for i below 100 sum i)))))

(test clear-resets
  (let ((s (make-fixnum-set)))
    (dotimes (i 1000) (fixnum-set-put i s))
    (fixnum-set-clear s)
    (is (= 0 (fixnum-set-count s)))
    (is (null (nth-value 1 (fixnum-set-get 7 s))))
    (fixnum-set-put 7 s)                     ; usable after clear
    (is-true (nth-value 1 (fixnum-set-get 7 s)))))

;; Randomized differential test against a CL hash-table.
(defun fuzz-set (n keymax)
  (let ((s (make-fixnum-set)) (ref (make-hash-table :test 'eql)) (bad 0))
    (dotimes (i n)
      (let ((k (random keymax)))
        (ecase (random 3)
          (0 (setf (gethash k ref) t) (fixnum-set-put k s))
          (1 (unless (eq (and (nth-value 1 (gethash k ref)) t)
                         (and (nth-value 1 (fixnum-set-get k s)) t))
               (incf bad)))
          (2 (remhash k ref) (fixnum-set-rem k s)))))
    (is (zerop bad) "presence matches reference")
    (is (= (hash-table-count ref) (fixnum-set-count s)) "count matches reference")
    (maphash (lambda (k v) (declare (ignore v))
               (unless (nth-value 1 (fixnum-set-get k s)) (incf bad)))
             ref)
    (is (zerop bad) "all reference members present")))

(defun fuzz-table (n keymax)
  (let ((h (make-str-table)) (ref (make-hash-table :test 'equal)) (bad 0))
    (dotimes (i n)
      (let ((k (format nil "k~a" (random keymax))))
        (ecase (random 3)
          (0 (let ((v (random 1000000))) (setf (gethash k ref) v) (str-table-put k v h)))
          (1 (multiple-value-bind (rv rp) (gethash k ref)
               (multiple-value-bind (hv hp) (str-table-get k h)
                 (unless (and (eq (and rp t) (and hp t)) (or (not rp) (eql rv hv)))
                   (incf bad)))))
          (2 (remhash k ref) (str-table-rem k h)))))
    (is (zerop bad) "presence+value match reference")
    (is (= (hash-table-count ref) (str-table-count h)))
    (maphash (lambda (k v)
               (unless (and (nth-value 1 (str-table-get k h)) (eql v (str-table-get k h))) (incf bad)))
             ref)
    (is (zerop bad))))

(test fuzz-set-churn   (fuzz-set 3000 40) (fuzz-set 100000 800) (fuzz-set 400000 25000))
(test fuzz-table-churn (fuzz-table 3000 40) (fuzz-table 100000 800) (fuzz-table 400000 25000))

;; Heavy delete/re-insert to force both grow and in-place compact.
(test grow-and-compact
  (let ((s (make-fixnum-set)) (ref (make-hash-table :test 'eql)))
    (dotimes (i 200000) (setf (gethash i ref) t) (fixnum-set-put i s))
    (dotimes (i 120000) (remhash i ref) (fixnum-set-rem i s))     ; tombstones
    (loop for i from 200000 below 350000 do (setf (gethash i ref) t) (fixnum-set-put i s))
    (is (= (hash-table-count ref) (fixnum-set-count s)))
    (let ((bad 0))
      (maphash (lambda (k v) (declare (ignore v))
                 (unless (nth-value 1 (fixnum-set-get k s)) (incf bad)))
               ref)
      (is (zerop bad)))))

;; :STORE-HASH keeps a parallel hash array that COMPACT reuses instead of
;; recomputing HASH-FN; churn (build/delete/re-add) forces compaction.
(test store-hash-option
  (let ((h (make-str-table-sh)) (ref (make-hash-table :test 'equal)) (bad 0))
    (dotimes (i 60000) (let ((k (format nil "s~a" i))) (setf (gethash k ref) i) (str-table-sh-put k i h)))
    (dotimes (i 30000) (let ((k (format nil "s~a" i))) (remhash k ref) (str-table-sh-rem k h)))  ; tombstones
    (dotimes (i 40000) (let ((k (format nil "t~a" i))) (setf (gethash k ref) i) (str-table-sh-put k i h)))  ; -> compact
    (is (= (hash-table-count ref) (str-table-sh-count h)))
    (maphash (lambda (k v) (unless (eql v (str-table-sh-get k h)) (incf bad))) ref)
    (is (zerop bad) "store-hash: entries intact after compact (hash reuse)")))
