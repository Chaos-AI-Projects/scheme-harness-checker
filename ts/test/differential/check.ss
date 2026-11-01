;; Differential driver for HC-17: runs termination.ss's check-termination, with an empty type-env as
;; test-termination.ss does, over every program source in the file named on the command line (one
;; written string per line) and writes, per program, ((kind function reason expr) ...), or (error)
;; when Scheme raises.
(import (rnrs) (harness-checker termination) (harness-checker whitelist-checker))
(define (viol->list v)
  (list (termination-violation-kind v) (termination-violation-function v)
        (termination-violation-reason v) (termination-violation-expr v)))
(let ((p (open-input-file (cadr (command-line)))))
  (let loop ()
    (let ((s (read p)))
      (unless (eof-object? s)
        (write (guard (e (#t (list 'error)))
                 (map viol->list (check-termination (read-all-expressions s) '()))))
        (newline)
        (loop)))))
