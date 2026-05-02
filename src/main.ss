;; main.ss
;; CLI entry point for the whitelist checker.
;;
;; Usage: scheme --libdirs src --program src/main.ss <source-file> <whitelist-file>
;;
;; Exit code 0 if no violations, 1 if violations found.

(import (rnrs) (harness-checker whitelist-checker))

(define (main args)
  (when (< (length args) 3)
    (display "Usage: scheme --libdirs src --program src/main.ss <source-file> <whitelist-file>")
    (newline)
    (exit 1))
  (let* ((source-path (cadr args))
         (whitelist-path (caddr args))
         (violations (check-file source-path whitelist-path)))
    (if (null? violations)
        (begin
          (display "OK: No whitelist violations found.") (newline)
          (exit 0))
        (begin
          (display "VIOLATIONS FOUND:") (newline)
          (for-each
           (lambda (v)
             (display "  - ")
             (display (violation-identifier v))
             (display " (")
             (display (violation-context v))
             (display ")")
             (newline))
           violations)
          (display (length violations))
          (display " violation(s) total.") (newline)
          (exit 1)))))

(main (command-line))
