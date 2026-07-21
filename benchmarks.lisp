(defpackage #:lp-hash-table/benchmark
  (:use #:cl #:lp-hash-table)
  (:local-nicknames (#:tb #:org.shirakumo.trivial-benchmark))
  (:export #:run-benchmarks))
(in-package #:lp-hash-table/benchmark)

;;;; Microbenchmarks vs native SBCL hash-tables.  Load the system and call
;;;; (lp-hash-table/benchmark:run-benchmarks).
;;;;
;;;; No key/index arrays and no linear key sequence are used anywhere.  Each
;;;; variant passes a GENERATOR EXPRESSION over a pseudo-random number X, spliced
;;;; inline; X comes from a full-period LCG stream (see LCG) -- never a 0,1,2,...
;;;; walk.  Because the LCG is full period, its first N outputs are DISTINCT, so
;;;; INSERT stores N distinct keys with no linear pattern and no backing array.
;;;; GET-HIT replays the stream from the fixed seed (every probe hits); GET-MISS
;;;; offsets X by 2^31 (always absent, the generator being injective in X).  The
;;;; pure lookups declare the probe key DYNAMIC-EXTENT, so a constructed key
;;;; (built with LIST/LIST*, not LOOP COLLECT) is stack-allocated -- probing
;;;; stays allocation-free.  BENCH emits one op suite per variant via a MACROLET.

;;; The multiplicative hashes and the LCG below keep every product under a
;;; 61-bit fixnum AND wrap it in (THE FIXNUM ...), so they stay native on ECL
;;; (61-bit fixnum) as well as SBCL (62-bit).  Two reasons a naive version goes
;;; generic (boxed) on ECL: (1) a 30-bit operand * the ~31.3-bit constant reaches
;;; 62 bits -- a fixnum on SBCL but a bignum on ECL -- so we mask operands to 29
;;; bits (30 for the LCG's smaller multiplier) to keep the product <=60.x bits;
;;; (2) even then, ECL does not propagate the LOGAND range bound through the
;;; multiply, so it can't prove the product is a fixnum -- (THE FIXNUM ...) (true
;;; thanks to the masking) forces the native machine multiply.  We also drop the
;;; (LOGAND ... MOST-POSITIVE-FIXNUM) masks: once the product provably fits a
;;; fixnum they are no-ops, and ECL compiles MOST-POSITIVE-FIXNUM as a runtime
;;; special-variable lookup rather than a constant.

(declaim (inline fxhash))
(defun fxhash (x)
  (declare (type fixnum x))
  (the fixnum (* (logand x #x1fffffff) 2654435769)))     ; 29-bit operand => <=60.3-bit product

(declaim (inline list-hash))
(defun list-hash (keys)
  "Order-sensitive multiplicative hash of a short list of fixnums; each step's
29-bit operand * 32-bit constant stays under a 61-bit fixnum."
  (declare (type list keys))
  (let ((h 0))
    (declare (type fixnum h))
    (dolist (e keys h)
      (setf h (the fixnum (* (logand (logxor h (the fixnum e)) #x1fffffff) 2654435769))))))

(declaim (inline lcg))
(defun lcg (x)
  "One step of a full-period 30-bit linear-congruential PRNG (Numerical Recipes
constants; Hull-Dobell holds, so the first 2^30 outputs are a permutation of
[0,2^30) -- hence distinct).  A 30-bit state keeps X*1103515245 at <=60.1 bits,
a fixnum on ECL too (a 31-bit state would reach 62 bits and overflow it)."
  (declare (type (unsigned-byte 30) x))
  (logand (the fixnum (+ (the fixnum (* x 1103515245)) 12345)) #x3fffffff))

(define-hash-set   fixnum-set    fxhash eq)
(define-hash-table list-table    list-hash equal)
(define-hash-table list-table-sh list-hash equal :store-hash t)

(defmacro timing (label repeat &body body)
  `(progn (format t "~&~%## ~a ##~%" ,label)
          (tb:with-timing (,repeat) ,@body)))

(defmacro bench (table-type native-test-fn n repeat gen &key store-hash set)
  "Emit the timing groups (insert / get-hit / get-miss / iterate / 50-50 churn)
comparing the lp type TABLE-TYPE against a native hash-table of test
NATIVE-TEST-FN, over N ops each, REPEAT times.  GEN is a key-generator
EXPRESSION over a pseudo-random number X, spliced inline (no key array).  X comes
from a full-period LCG stream (via (SETF R (LCG R))), not a linear sequence:
INSERT walks N distinct stream values; GET-HIT replays the same stream from the
fixed seed R=1 (so it hits); GET-MISS offsets X by 2^31 (absent, GEN injective).
  :SET t             TABLE-TYPE is a set (1-arg PUT, 1-arg MAP, no values).
  :STORE-HASH <type> also bench the store-hash sibling lp type <type>."
  (let* ((desc (string-downcase (symbol-name table-type)))
         (ntag (format nil "native ~(~a~)" native-test-fn))
         (vars (cons (list table-type "lp" (gensym "TB"))
                     (when store-hash
                       (list (list store-hash "lp store-hash" (gensym "TS")))))))
    ;; The MACROLET carries only the per-type operations (PUT/PGET/DEL/SWEEP take
    ;; the lp type as their first argument; NPUT/LAB are native-side helpers);
    ;; the PRNG stepping (SETF R (LCG R)) and the loops are written out inline.
    `(let* ((n ,n) (repeat ,repeat) (m (max 1 (floor n 2))) (r 1))
       (declare (type fixnum n m) (type (unsigned-byte 30) r))
       (macrolet ((mk    (ty)      `(,(alexandria:symbolicate '#:make- ty)))
                  (put   (ty k tb) ,(if set '`(,(alexandria:symbolicate ty '#:-put) ,k ,tb)
                                            '`(,(alexandria:symbolicate ty '#:-put) ,k ,k ,tb)))
                  (pget  (ty k tb) `(,(alexandria:symbolicate ty '#:-get) ,k ,tb))
                  (del   (ty k tb) `(,(alexandria:symbolicate ty '#:-rem) ,k ,tb))
                  (nput  (k h)     ,(if set '`(setf (gethash ,k ,h) t)
                                            '`(setf (gethash ,k ,h) ,k)))
                  (sweep (ty tb)   ,(if set '`(,(alexandria:symbolicate '#:map- ty)
                                                (lambda (k) (declare (ignore k)) (incf acc)) ,tb)
                                            '`(,(alexandria:symbolicate '#:map- ty)
                                                (lambda (k v) (declare (ignore k v)) (incf acc)) ,tb)))
                  (lab   (op tag)  (format nil "~a -- ~a (~a)" op ,desc tag)))
         ;; ---- insert N distinct PRNG-stream keys (fresh table each) ----
         ,@(loop for (ty tag) in vars
                 collect `(timing (lab "insert" ,tag) repeat
                            (let ((tb (mk ,ty)))
                              (setf r 1)
                              (dotimes (iter n)
                                (let* ((x (setf r (lcg r))) (k ,gen)) (put ,ty k tb))))))
         (timing (lab "insert" ,ntag) repeat
           (let ((h (make-hash-table :test ',native-test-fn)))
             (setf r 1)
             (dotimes (iter n)
               (let* ((x (setf r (lcg r))) (k ,gen)) (nput k h)))))
         ;; ---- get-hit / get-miss / iterate (shared populated tables) ----
         (let (,@(loop for (ty tag var) in vars collect `(,var (mk ,ty)))
               (h (make-hash-table :test ',native-test-fn)) (acc 0))
           (declare (type fixnum acc))
           (setf r 1)
           (dotimes (iter n)
             (let* ((x (setf r (lcg r))) (k ,gen))
               ,@(loop for (ty tag var) in vars collect `(put ,ty k ,var))
               (nput k h)))
           ;; GET-HIT: replay the populate stream from the seed => every key present.
           ;; Each lookup's presence flag is accumulated into ACC (used at the end),
           ;; so the compiler can't dead-code-eliminate the result-unused lookups --
           ;; ECL silently drops a bare (gethash k h), which would make native look
           ;; ~free and wildly overstate the lp/native gap.
           ,@(loop for (ty tag var) in vars
                   collect `(timing (lab "get-hit" ,tag) repeat
                              (setf r 1)
                              (dotimes (iter n)
                                (let* ((x (setf r (lcg r))) (k ,gen))
                                  (declare (dynamic-extent k))
                                  (when (nth-value 1 (pget ,ty k ,var)) (incf acc))))))
           (timing (lab "get-hit" ,ntag) repeat
             (setf r 1)
             (dotimes (iter n)
               (let* ((x (setf r (lcg r))) (k ,gen))
                 (declare (dynamic-extent k))
                 (when (nth-value 1 (gethash k h)) (incf acc)))))
           ;; GET-MISS: stream offset by 2^31 => key disjoint from any present key
           ,@(loop for (ty tag var) in vars
                   collect `(timing (lab "get-miss" ,tag) repeat
                              (dotimes (iter n)
                                (let* ((x (the fixnum (+ #x80000000 (setf r (lcg r))))) (k ,gen))
                                  (declare (dynamic-extent k))
                                  (when (nth-value 1 (pget ,ty k ,var)) (incf acc))))))
           (timing (lab "get-miss" ,ntag) repeat
             (dotimes (iter n)
               (let* ((x (the fixnum (+ #x80000000 (setf r (lcg r))))) (k ,gen))
                 (declare (dynamic-extent k))
                 (when (nth-value 1 (gethash k h)) (incf acc)))))
           ;; ITERATE accumulates into the same ACC (no reset), keeping it live.
           ,@(loop for (ty tag var) in vars
                   collect `(timing (lab "iterate" ,tag) repeat (sweep ,ty ,var)))
           (timing (lab "iterate" ,ntag) repeat
             (maphash (lambda (k v) (declare (ignore k v)) (incf acc)) h))
           (unless (plusp acc) (error "sanity: nothing accumulated")))
         ;; ---- 50% insert / 50% delete over a bounded PRNG keyspace [0,M) ----
         ;; PUT stores the key => it must be heap.  DEL only probes with the key
         ;; (never retains it), so build DEL's key with DYNAMIC-EXTENT: the
         ;; lookup path allocates nothing (for list keys the stack-consed probe
         ;; key is reclaimed on loop exit).  Keys are built per-branch, so the
         ;; transient half of the churn never touches the heap.
         ,@(loop for (ty tag) in vars
                 collect `(timing (lab "50/50 churn" ,tag) repeat
                            (let ((tb (mk ,ty)))
                              (dotimes (iter n)
                                (let ((x (rem (setf r (lcg r)) m)))
                                  (declare (type fixnum x))
                                  (if (logbitp 20 r)
                                      (let ((k ,gen)) (put ,ty k tb))                                 ; stored => heap
                                      (let ((k ,gen)) (declare (dynamic-extent k)) (del ,ty k tb)))))))) ; transient => stack
         (timing (lab "50/50 churn" ,ntag) repeat
           (let ((h (make-hash-table :test ',native-test-fn)))
             (dotimes (iter n)
               (let ((x (rem (setf r (lcg r)) m)))
                 (declare (type fixnum x))
                 (if (logbitp 20 r)
                     (let ((k ,gen)) (nput k h))
                     (let ((k ,gen)) (declare (dynamic-extent k)) (remhash k h)))))))))))

(defun run-benchmarks (&key (n 2000000) (repeat 7))
  "Run the LP-vs-native microbenchmark suite (N ops each, REPEAT times) over two
key-type variants: fixnums and short lists of fixnums."
  (declare (type fixnum n))
  (format t "~&===== lp-hash-table microbenchmarks (~a ops, ~a repeats) =====~%" n repeat)
  (bench fixnum-set eql n repeat
         x                                                  ; key = the PRNG value itself (no allocation)
         :set t)
  (bench list-table equal n repeat
         (list x (logand x #xff) (ash x -8) (ash x -16))    ; length-4 list, headed by X => injective;
         :store-hash list-table-sh)                         ; LIST (not LOOP) => stack-allocatable
  (values))
