;; Differential driver for HC-17: runs termination.ss's alpha-rename-definitions over every program
;; source in the file named on the command line (one written string per line) and writes, per
;; program, (renamed-program top-env), or (error) when Scheme raises.
(import (rnrs) (harness-checker termination) (harness-checker whitelist-checker))
(let ((p (open-input-file (cadr (command-line)))))
  (let loop ()
    (let ((s (read p)))
      (unless (eof-object? s)
        (write (guard (e (#t (list 'error)))
                 (let-values (((renamed top-env) (alpha-rename-definitions (read-all-expressions s))))
                   (list renamed top-env))))
        (newline)
        (loop)))))
