;; main.ss
;; CLI entry point for the whitelist checker, type checker, and termination analysis.
;;
;; Usage:
;;   scheme --libdirs src:<packrat-extended-path>:<packrat-examples-path> --program src/main.ss [--no-termination] [--termination-depth N] [--tool-schemas <path>] <source-file> <whitelist-file> [<type-signatures-file>]
;;
;; Flags:
;;   --no-termination       Disable termination analysis pass (enabled by default)
;;   --termination-depth N  Skip call-graph analysis if program has more than N definitions
;;   --tool-schemas <path>  Load tool JSON Schemas from file, merge with type signatures
;;
;; Exit code 0 if no violations, 1 if violations found.

(import (rnrs)
        (harness-checker whitelist-checker)
        (harness-checker types)
        (harness-checker pass1-constraints)
        (harness-checker type-infer)
        (harness-checker termination)
        (harness-checker schema-registry))

;; Flags that consume the next argument as their value
(define flags-with-value '("--termination-depth" "--tool-schemas"))

;; Extract --flags from args, returning (flags . positional-args)
;; Flags listed in flags-with-value consume the following argument as a value,
;; stored as (flag . value) in the flags list.
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
       (if (and (member (car remaining) flags-with-value)
                (pair? (cdr remaining)))
           ;; Flag with value: consume next arg
           (loop (cddr remaining)
                 (cons (cons (car remaining) (cadr remaining)) flags)
                 positional)
           ;; Boolean flag
           (loop (cdr remaining)
                 (cons (car remaining) flags)
                 positional)))
      (else
       (loop (cdr remaining)
             flags
             (cons (car remaining) positional))))))

;; Look up a flag-with-value from the parsed flags list.
;; Returns the string value or #f if not present.
(define (get-flag-value flags flag-name)
  (let loop ((remaining flags))
    (cond
      ((null? remaining) #f)
      ((and (pair? (car remaining))
            (string=? (caar remaining) flag-name))
       (cdar remaining))
      (else (loop (cdr remaining))))))

;; Check if a boolean flag is present in the flags list.
(define (has-flag? flags flag-name)
  (let loop ((remaining flags))
    (cond
      ((null? remaining) #f)
      ((and (string? (car remaining))
            (string=? (car remaining) flag-name)) #t)
      (else (loop (cdr remaining))))))

(define (main args)
  (let* ((parsed (parse-flags args))
         (flags (car parsed))
         (positional (cdr parsed))
         (termination-enabled? (not (has-flag? flags "--no-termination")))
         (termination-depth-str (get-flag-value flags "--termination-depth"))
         (termination-depth (if termination-depth-str
                                (string->number termination-depth-str)
                                #f))
         (tool-schemas-path (get-flag-value flags "--tool-schemas")))
    (when (< (length positional) 2)
      (display "Usage: scheme --libdirs src --program src/main.ss [--no-termination] [--termination-depth N] [--tool-schemas <path>] <source-file> <whitelist-file> [<type-signatures-file>]")
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
    ;; Merge with tool schemas if --tool-schemas is specified
    (let ((signatures (let ((base-sigs (if signatures-path
                                           (load-type-signatures signatures-path)
                                           '()))
                            (tool-sigs (if tool-schemas-path
                                           (load-tool-schemas tool-schemas-path)
                                           '())))
                        ;; Tool schemas first: assq finds first match, so tool-specific
                        ;; types take precedence over base signatures
                        (append tool-sigs base-sigs))))

    ;; Run type checker if any type information is available
    (let ((type-errors '())
          (constraint-errors '()))
      (when (not (null? signatures))
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
          (let ((tv (if termination-depth
                        (check-termination exprs signatures termination-depth)
                        (check-termination exprs signatures))))
            (set! term-violations tv)))

        ;; Report termination violations
        (unless (null? term-violations)
          (display "TERMINATION VIOLATIONS:") (newline)
          (for-each
           (lambda (v)
             (display "    - ")
             (display (termination-violation-kind v))
             (display ": ")
             (display (termination-violation-reason v))
             (newline)
             (display "        at: ")
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
