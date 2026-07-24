;;; Many TYPE declaration/THE here is unnecessary for SBCL, but good
;;; for not-so-smart implementations like CCL and ECL

(in-package #:lp-hash-table)

(defvar *probe-bits* (min 32 (1- (integer-length most-positive-fixnum)))
  "Default bit width for probe vector.")

(defvar +deleted+ '#:deleted
  "Marker stored in a KV entry's key cell when it has been removed.")

(declaim (inline %pow2-ceiling))
(defun %pow2-ceiling (n)
  "Least power of two >= N, floored at 16."
  (ash 1 (max 4 (integer-length (1- (max 1 n))))))

(deftype function-designator () `(or symbol (cons (eql lambda))))

(defun %generate (name hash-fn test-fn valuep store-hash optimize probe-bits)
  (check-type name symbol)
  (check-type hash-fn function-designator)
  (check-type test-fn function-designator)
  (let ((u32 `(unsigned-byte ,probe-bits))
        (u33 `(unsigned-byte ,(1+ probe-bits)))
        (%make   (symbolicate '#:%make- name))
        (make    (symbolicate '#:make- name))
        (get*    (symbolicate name '#:-get))
        (put*    (symbolicate name '#:-put))
        (rem*    (symbolicate name '#:-rem))
        (clear   (symbolicate name '#:-clear))
        (mapf    (symbolicate '#:map- name))
        (grow    (symbolicate '#:% name '#:-grow))
        (compact (symbolicate '#:% name '#:-compact))
        (pfind   (symbolicate '#:% name '#:-probe))
        (probe   (symbolicate name '#:-probe))
        (kv      (symbolicate name '#:-kv))
        (imask   (symbolicate name '#:-imask))
        (icount  (symbolicate name '#:-count))
        (hwm     (symbolicate name '#:-hwm))
        (ilimit  (symbolicate name '#:-ilimit))
        (lff     (symbolicate name '#:-load-factor))
        (kvsf    (symbolicate name '#:-kv-size))
        (hashvec (symbolicate name '#:-hashes)))   ; per-entry hash32 (store-hash only)

    `(progn
       (declaim (inline ,probe ,kv ,imask ,icount ,hwm ,ilimit ,lff ,kvsf ,@(when store-hash '(hash-vec))))
       ;; CCL 1.13 can't open-code struct accessors if DEFSTRUCT and
       ;; callers sit in the same MACROLET
       (macrolet ((lose () '(error "don't call internal constructor")))
         (defstruct (,name (:constructor ,%make) (:copier nil) (:predicate nil))
           (probe (error "don't call internal constructor") :type (simple-array ,u32 (*)))
           (kv (error "don't call internal constructor") :type simple-vector)
           (imask 15 :type ,u32)
           (count 0 :type ,u32)
           (hwm 0 :type ,u32)
           (ilimit 11 :type ,u32)
           (load-factor 0.7)
           (kv-size 1.5)
           ,@(when store-hash
               `((hashes (make-array 0 :element-type ',u32)
                         :type (simple-array ,u32 (*)))))))

       (declaim (inline ,mapf ,pfind))
       (macrolet ((eref (p s) `(aref ,p (the fixnum (1+ (the fixnum (ash ,s 1)))))) ; probe entry-index+1
                  (href (p s) `(aref ,p (the fixnum (ash ,s 1)))) ; probe hash32
                  (ksize (n) ,(if valuep '`(the fixnum (ash ,n 1)) 'n)) ; kv size for N entries
                  (kref (v i) ,(if valuep '`(svref ,v (the fixnum (ash ,i 1))) '`(svref ,v ,i))) ; entry I key
                  (vref (v i) `(svref ,v (the fixnum (1+ (the fixnum (ash ,i 1)))))) ; entry I value (table only)
                  (next (s m) `(the ,',u32 (logand (the fixnum (1+ ,s)) ,m))) ; probe advance
                  (hashof (k) `(logand (the fixnum (,',hash-fn ,k)) ,,(1- (ash 1 probe-bits))))
                  (lose () '(error "don't call internal constructor"))
                  (check-cap (cap)
                    `(if (<= ,cap ,,(ash 1 probe-bits))
                         ,cap
                         (error "capacity ~a too large" ,cap)))
                  (check-klim (klim)
                    `(if (< ,klim ,,(1- (ash 1 probe-bits)))
                         ,klim
                         (error "kv size ~a too large" ,klim))))

         (defun ,make (&key (size 16) (load-factor 0.7) (kv-size 1.5))
           (assert (< 0 load-factor 1) (load-factor)
                   "load-factor must be in (0,1), got ~a" load-factor)
           (assert (> kv-size 1) (kv-size)
                   "kv-size must be > 1, got ~a" kv-size)
           (let* ((cap (check-cap (%pow2-ceiling size)))
                  (lim (floor (* cap load-factor)))
                  (klim (check-klim (ceiling (* cap load-factor kv-size)))))
             (declare (type ,u33 cap) (type ,u32 lim klim))
             (,%make :probe (make-array (* 2 cap) :element-type ',u32
                                                  :initial-element 0)
                     :kv (make-array (ksize klim))
                     ,@(when store-hash
                         `(:hashes (make-array klim :element-type ',u32 :initial-element 0)))
                     :load-factor load-factor :kv-size kv-size
                     :imask (1- cap) :ilimit lim)))

         (defun ,pfind (pr ks imask h32 key)
           "Return (VALUES SLOT I). If KEY is present, I is its entry index and
SLOT its probe slot; else I = -1 and SLOT is the empty slot where it
belongs.  H32 = 32-bit key hash.  Shared by GET/PUT/REM."
           (declare (optimize ,@optimize)
                    (type (simple-array ,u32 (*)) pr) (type simple-vector ks)
                    (type ,u32 imask h32) (ignorable ks key))
           (let ((slot (logand h32 imask)))
             (declare (type ,u32 slot))
             (loop
               (let ((e (eref pr slot)))
                 (declare (type ,u32 e))
                 (when (zerop e) (return (values slot -1)))
                 (when (= (href pr slot) h32)
                   (let ((i (1- e)))
                     (declare (type ,u32 i))
                     (when (,test-fn (kref ks i) key) (return (values slot i)))))
                 (setq slot (next slot imask))))))

         ;; GROW (COUNT reached ILIMIT): allocate probe+kv at 2x capacity, copy kv
         ;; (entry indices unchanged) and rebuild the probe reusing (hash32, index+1).
         (defun ,grow (table)
           (let* ((pr (,probe table)) (ok (,kv table))
                  (hwm (,hwm table)) (cap (1+ (,imask table)))
                  (ncap (check-cap (* 2 cap))) (nimask (1- ncap)) (nlim (floor (* ncap (,lff table))))
                  (nklim (check-klim (ceiling (* ncap (,lff table) (,kvsf table)))))
                  (np (make-array (* 2 ncap) :element-type ',u32 :initial-element 0))
                  (nk (make-array (ksize nklim)))
                  ,@(when store-hash
                      `((nh (make-array nklim :element-type ',u32 :initial-element 0)))))
             (declare (type (simple-array ,u32 (*)) pr np) (type simple-vector ok nk)
                      (type ,u33 cap ncap) (type ,u32 nlim nklim hwm nimask))
             (replace nk ok :end2 (ksize hwm))
             ,@(when store-hash `((replace nh (,hashvec table) :end2 hwm)))
             (dotimes (s cap)
               (declare (optimize ,@optimize))
               (let ((e (eref pr s)))
                 (declare (type ,u32 e))
                 (unless (zerop e)
                   (let ((h32 (href pr s)) (slot (logand (href pr s) nimask)))
                     (declare (type ,u32 h32 slot))
                     (loop
                       (when (zerop (eref np slot))
                         (setf (href np slot) h32 (eref np slot) e) (return))
                       (setq slot (next slot nimask)))))))
             (setf (,probe table) np (,kv table) nk (,imask table) nimask (,ilimit table) nlim
                   ,@(when store-hash `((,hashvec table) nh)))))

         ;; COMPACT (KV full, probe not): reclaim IN PLACE -- pack survivors left,
         ;; clear the vacated tail (GC-scanned), then clear the probe and reinsert.
         (defun ,compact (table)
           (let* ((ks (,kv table)) (pr (,probe table)) (imask (,imask table))
                  ,@(when store-hash `((hv (,hashvec table))))
                  (hwm (,hwm table)) (j 0))
             (declare (type (simple-array ,u32 (*)) pr) (type simple-vector ks)
                      (type ,u32 imask hwm j)
                      ,@(when store-hash `((type (simple-array ,u32 (*)) hv))))
             (dotimes (i hwm)
               (declare (optimize ,@optimize)
                        (type ,u32 i))
               (let ((k (kref ks i)))
                 (unless (eq k +deleted+)
                   (setf (kref ks j) k
                         ,@(when valuep '((vref ks j) (vref ks i)))
                         ,@(when store-hash '((aref hv j) (aref hv i))))
                   (incf j))))
             (fill ks 0 :start (ksize j) :end (ksize hwm))
             (fill pr 0)
             (dotimes (m j)
               (declare (optimize ,@optimize)
                        (type ,u32 m))
               (let ((h32 ,(if store-hash '(aref hv m) '(hashof (kref ks m))))
                     (slot 0))
                 (declare (type ,u32 h32 slot))
                 (setq slot (logand h32 imask))
                 (loop
                   (when (zerop (eref pr slot))
                     (setf (href pr slot) h32 (eref pr slot) (the ,u32 (1+ m)))
                     (return))
                   (setq slot (next slot imask)))))
             (setf (,hwm table) j (,icount table) j)))

         (defun ,get* (key table &optional default)
           (declare (optimize ,@optimize) (type ,name table))
           (let ((ks (,kv table)) (h32 (hashof key)))
             (declare (type simple-vector ks) (type ,u32 h32))
             (multiple-value-bind (slot i) (,pfind (,probe table) ks (,imask table) h32 key)
               (declare (ignore slot) (type fixnum i))
               (if (minusp i)
                   (values default nil)
                   (values ,(if valuep '(vref ks i) '(kref ks i)) t)))))

         (defun ,put* (key ,@(when valuep '(value)) table)
           (declare (optimize ,@optimize) (type ,name table))
           (cond ((>= (,icount table) (,ilimit table)) (,grow table))
                 ((>= (ksize (,hwm table)) (length (,kv table))) (,compact table))) ; KV full
           (let* ((pr (,probe table)) (ks (,kv table)) (h32 (hashof key)))
             (declare (type (simple-array ,u32 (*)) pr) (type simple-vector ks)
                      (type ,u32 h32))
             (multiple-value-bind (slot i) (,pfind pr ks (,imask table) h32 key)
               (declare (type ,u32 slot) (type fixnum i))
               (cond ((>= i 0)     ; present: update / return existing
                      ,@(when valuep '((setf (vref ks i) value)))
                      ,(if valuep 'value '(kref ks i)))
                     (t        ; absent: append at HWM into empty SLOT
                      (let ((n (,hwm table)))
                        (declare (type ,u32 n))
                        (setf (kref ks n) key
                              ,@(when valuep '((vref ks n) value))
                              ,@(when store-hash `((aref (,hashvec table) n) h32))
                              (href pr slot) h32
                              (eref pr slot) (the ,u32 (1+ n)))
                        (incf (,hwm table)) (incf (,icount table))
                        ,(if valuep 'value '(kref ks n))))))))

         (defun ,rem* (key table)
           (declare (optimize ,@optimize) (type ,name table))
           (let* ((pr (,probe table)) (ks (,kv table)) (imask (,imask table)) (h32 (hashof key)))
             (declare (type (simple-array ,u32 (*)) pr) (type simple-vector ks)
                      (type ,u32 imask h32))
             (multiple-value-bind (slot i) (,pfind pr ks imask h32 key)
               (declare (type ,u32 slot) (type fixnum i))
               (when (minusp i) (return-from ,rem* nil))
               (setf (kref ks i) +deleted+ ,@(when valuep '((vref ks i) nil)))
               (decf (,icount table))
               (let ((si slot) (sj slot)) ; Knuth backward-shift on PROBE from SLOT
                 (declare (type ,u32 si sj))
                 (loop
                   (setq sj (next sj imask))
                   (let ((e (eref pr sj)))
                     (declare (type ,u32 e))
                     (when (zerop e) (setf (eref pr si) 0) (return t))
                     (let ((home (logand (href pr sj) imask)))
                       (declare (type ,u32 home))
                       (unless (if (<= si sj) (and (< si home) (<= home sj))
                                   (or (< si home) (<= home sj)))
                         (setf (href pr si) (href pr sj) (eref pr si) e)
                         (setq si sj)))))))))

         (defun ,clear (table)
           (fill (,probe table) 0)
           (fill (,kv table) +deleted+)
           (setf (,icount table) 0 (,hwm table) 0)
           table)

         (defun ,mapf (function table)
           (let ((ks (,kv table)) (hwm (,hwm table)))
             (declare (type simple-vector ks) (type ,u32 hwm))
             (loop for i of-type ,u32 from 0 below hwm
                   for k = (kref ks i)
                   unless (eq k +deleted+)
                     do ,(if valuep '(funcall function k (vref ks i))
                             '(funcall function k)))
             nil))

         ',name))))

(defmacro define-hash-table
    (name hash-fn test-fn
     &key store-hash (optimize '(speed)) (probe-bits *probe-bits*))
  "Define a hash table type NAME.

Generates MAKE-NAME, NAME-GET/PUT/REM/CLEAR and MAP-NAME (preserves
insertion order). Also generate %NAME-GROW/COMPACT/PROBE, use if you
know what you are doing.

HASH-FN and TEST-FN are unevaluated function designators. :STORE-HASH T keeps a
parallel (unsigned-byte 32) hash array so COMPACT reuses stored hashes instead
of recomputing HASH-FN, use it for an expensive HASH-FN with delete-heavy
workload. :OPTIMIZE specifies optimization declaration."
  (%generate name hash-fn test-fn t store-hash optimize probe-bits))

(defmacro define-hash-set
    (name hash-fn test-fn
     &key store-hash (optimize '(speed)) (probe-bits *probe-bits*))
  "Define a hash set type NAME.

Generates MAKE-NAME, NAME-GET/PUT/REM/CLEAR and MAP-NAME (preserves
insertion order). Also generate %NAME-GROW/COMPACT/PROBE, use if you
know what you are doing.

HASH-FN and TEST-FN are unevaluated function designators. :STORE-HASH T keeps a
parallel (unsigned-byte 32) hash array so COMPACT reuses stored hashes instead
of recomputing HASH-FN, use it for an expensive HASH-FN with delete-heavy
workload. :OPTIMIZE specifies optimization declaration."
  (%generate name hash-fn test-fn nil store-hash optimize probe-bits))
