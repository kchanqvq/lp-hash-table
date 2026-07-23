(defpackage #:lp-hash-table
  (:use #:cl #:alexandria)
  (:nicknames #:lpht)
  (:export #:*probe-bits*
           #:define-hash-table
           #:define-hash-set))
