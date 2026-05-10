;; main.ss
;; CLI entry point for the whitelist checker, type checker, and termination analysis.
;;
;; Usage:
;;   scheme --libdirs src:<packrat-extended-path> --program src/main.ss [--termination] <source-file> <whitelist-file> [<type-signatures-file>]
;;
;; Flags:
;;   --termination  Enable termination analysis pass (disabled by default)
;;
;; Exit code 0 if no violations, 1 if violations found.

(import (rnrs)
        (harness-checker whitelist-checker)
        (harness-checker types)
        (harness-checker pass1-constraints)
        (harness-checker type-infer)
        (harness-checker termination))

;; Extract --flags from args, returning (flags . positional-args)
(define (parse-flags args)
  (let loop ((remaining (cdr args))  ;; skip program name
             (flags '())
             (positional '()))
    (cond
      ((null? remaining)
       (cons flags (reverse positional)))
      ((and (string? (car remaining))
            (> (string-length (car remaining)) 2)
            (char=? (string-ref (car remaining) 0) #\-)
            (char=? (string-ref (car remaining) 1) #\-))
       (loop (cdr remaining)
             (cons (car remaining) flags)
             positional))
      (else
       (loop (cdr remaining)
             flags
             (cons (car remaining) positional))))))

(define (main args)
  (let* ((parsed (parse-flags args))
         (flags (car parsed))
         (positional (cdr parsed))
         (termination-enabled? (member "--termination" flags)))
    (when (< (length positional) 2)
      (display "Usage: scheme --libdirs src --program src/main.ss [--termination] <source-file> <whitelist-file> [<type-signatures-file>]")
      (newline)
      (exit 1))
    (let* ((source-path (car positional))
           (whitelist-path (cadr positional))
           (signatures-path (if (> (length positional) 2) (caddr positional) #f))
           (source-str (read-source-file source-path))
           (exprs (read-all-expressions source-str))
           (whitelist (load-whitelist whitelist-path))
           (wl-violations (check-expressions exprs whitelist)))

    ;; Report whitelist violations
    (unless (null? wl-violations)
      (display "WHITELIST VIOLATIONS:") (newline)
      (for-each
       (lambda (v)
         (display "  - ")
         (display (wl-violation-identifier v))
         (display " (")
         (display (wl-violation-context v))
         (display ")")
         (newline))
       wl-violations))

    ;; Load type signatures once if provided (shared by type checker and termination analysis)
    (let ((signatures (if signatures-path
                          (load-type-signatures signatures-path)
                          '())))

    ;; Run type checker if signatures file provided
    (let ((type-errors '())
          (constraint-errors '()))
      (when signatures-path
        (let* (;; Pass 1: infer parameter constraints
               (pass1-result (infer-param-constraints exprs signatures))
               (param-types (car pass1-result))
               (param-arities (cadr pass1-result))
               (p1-errors (caddr pass1-result))
               ;; Pass 2: type inference and call-site checking
               (p2-errors (check-types exprs signatures param-types param-arities)))
          (set! constraint-errors p1-errors)
          (set! type-errors p2-errors)))

      ;; Report constraint errors (Pass 1)
      (unless (null? constraint-errors)
        (display "CONSTRAINT ERRORS:") (newline)
        (for-each
         (lambda (err)
           (display "  - parameter '")
           (display (constraint-error-param err))
           (display "' has contradictory constraints: ")
           (let ((types (constraint-error-constraints err)))
             (let loop ((remaining types) (first? #t))
               (when (pair? remaining)
                 (unless first? (display " vs "))
                 (display (type->string (car remaining)))
                 (loop (cdr remaining) #f))))
           (newline)
           (let ((sources (constraint-error-sources err)))
             (for-each
              (lambda (src)
                (display "      from: ")
                (write src)
                (newline))
              sources)))
         constraint-errors))

      ;; Report type errors (Pass 2)
      (unless (null? type-errors)
        (display "TYPE ERRORS:") (newline)
        (for-each
         (lambda (err)
           (case (type-error-kind err)
             ((arity)
              (display "  - ")
              (display (type-error-function err))
              (display ": expected ")
              (display (type-error-expected err))
              (display " argument(s), got ")
              (display (type-error-actual err))
              (newline)
              (display "      at: ")
              (write (type-error-expr err))
              (newline))
             ((type-mismatch)
              (display "  - ")
              (display (type-error-function err))
              (display " argument ")
              (display (type-error-position err))
              (display ": expected ")
              (display (type-error-expected err))
              (display ", got ")
              (display (type-error-actual err))
              (newline)
              (display "      at: ")
              (write (type-error-expr err))
              (newline))))
         type-errors))

      ;; Run termination analysis if enabled
      (let ((term-violations '()))
        (when termination-enabled?
          (let ((tv (check-termination exprs signatures)))
            (set! term-violations tv)))

        ;; Report termination violations
        (unless (null? term-violations)
          (display "TERMINATION VIOLATIONS:") (newline)
          (for-each
           (lambda (v)
             (display "  - ")
             (display (termination-violation-kind v))
             (when (termination-violation-function v)
               (display " in ")
               (display (termination-violation-function v)))
             (display ": ")
             (display (termination-violation-reason v))
             (newline)
             (display "      at: ")
             (write (termination-violation-expr v))
             (newline))
           term-violations))

      ;; Final summary and exit
      (let ((total-violations (+ (length wl-violations)
                                 (length constraint-errors)
                                 (length type-errors)
                                 (length term-violations))))
        (if (= total-violations 0)
            (begin
              (display "OK: No violations found.") (newline)
              (exit 0))
            (begin
              (display total-violations)
              (display " violation(s) total.") (newline)
              (exit 1))))))))))

;; Read source file contents as a string
(define (read-source-file path)
  (let* ((port (open-input-file path))
         (content (get-string-all port)))
    (close-port port)
    content))

(main (command-line))
