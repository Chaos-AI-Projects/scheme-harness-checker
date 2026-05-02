;; sample-unsafe.ss
;; A sample program that should FAIL the whitelist checker.
;; Contains calls to dangerous functions: system, eval, delete-file

(define (do-something)
  (system "rm -rf /tmp/data")
  (eval '(+ 1 2))
  (delete-file "/etc/important"))

(do-something)
