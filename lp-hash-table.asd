(asdf:defsystem #:lp-hash-table
  :description "Pretty fast insertion-ordered linear-probing hash tables and sets"
  :author "Qiantan Hong <qthong@stanford.edu>"
  :license "Public Domain"
  :serial t
  :depends-on (:alexandria)
  :components ((:file "package")
               (:file "lp-hash-table"))
  :in-order-to ((test-op (test-op "lp-hash-table/test"))))

(asdf:defsystem #:lp-hash-table/test
  :depends-on (:lp-hash-table :fiveam)
  :serial t
  :components ((:file "tests"))
  :perform (test-op (o c)
             (unless (uiop:symbol-call '#:fiveam '#:run!
                                       (uiop:find-symbol* '#:all '#:lp-hash-table/test))
               (error "lp-hash-table test failures"))))

(asdf:defsystem #:lp-hash-table/benchmark
  :depends-on (:lp-hash-table :trivial-benchmark)
  :serial t
  :components ((:file "benchmarks"))
  :perform (test-op (o c)
             (uiop:symbol-call '#:lp-hash-table/benchmark '#:run-benchmarks)))
