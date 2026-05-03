;; whitelist-checker.ss
;; Function Whitelist Checker for LLM-generated Scheme programs.
;;
;; Approach:
;;   1. Use `read` to parse source into s-expressions
;;   2. Walk the tree with an abstract evaluator tracking bindings
;;      from: define, let, lambda, letrec
;;   3. Collect unbound identifiers (external dependencies)
;;   4. Compare against a deny-by-default whitelist
;;
;; The result is a list of violations: identifiers the program uses
;; that are not locally defined and not in the whitelist.

(library (harness-checker whitelist-checker)
  (export check-file
          check-source
          check-expressions
          read-all-expressions
          collect-unbound
          load-whitelist
          wl-violation-identifier
          wl-violation-context)
  (import (rnrs))

  ;; A violation record: an unbound identifier not in the whitelist
  (define-record-type wl-violation
    (fields identifier context))

  ;; Read all s-expressions from a string
  (define (read-all-expressions source)
    (let ((port (open-string-input-port source)))
      (let loop ((exprs '()))
        (let ((expr (read port)))
          (if (eof-object? expr)
              (reverse exprs)
              (loop (cons expr exprs)))))))

  ;; Read all s-expressions from a file
  (define (read-file path)
    (let ((port (open-input-file path)))
      (let loop ((exprs '()))
        (let ((expr (read port)))
          (if (eof-object? expr)
              (begin (close-port port) (reverse exprs))
              (loop (cons expr exprs)))))))

  ;; Load whitelist from a file (one identifier per line)
  (define (load-whitelist path)
    (let ((port (open-input-file path)))
      (let loop ((ids '()))
        (let ((line (get-line port)))
          (if (eof-object? line)
              (begin (close-port port) ids)
              (let ((trimmed (string-trim line)))
                (if (or (string=? trimmed "")
                        (char=? (string-ref trimmed 0) #\;))
                    (loop ids)
                    (loop (cons (string->symbol trimmed) ids)))))))))

  ;; Trim whitespace from a string
  (define (string-trim s)
    (let* ((len (string-length s))
           (start (let loop ((i 0))
                    (if (and (< i len) (char-whitespace? (string-ref s i)))
                        (loop (+ i 1))
                        i)))
           (end (let loop ((i len))
                  (if (and (> i start) (char-whitespace? (string-ref s (- i 1))))
                      (loop (- i 1))
                      i))))
      (substring s start end)))

  ;; Collect all unbound identifiers from a list of expressions.
  ;; `env` is a list of symbols that are currently bound.
  ;; Returns a list of symbols (may contain duplicates).
  (define (collect-unbound exprs)
    (let ((unbound '()))
      (define (walk expr env)
        (cond
          ((symbol? expr)
           (unless (memq expr env)
             (set! unbound (cons expr unbound))))
          ((not (pair? expr)) (values))
          (else
           (let ((head (car expr)))
             (cond
               ;; (define name expr) or (define (name . params) body ...)
               ((eq? head 'define)
                (walk-define (cdr expr) env))
               ;; (lambda (params ...) body ...)
               ((eq? head 'lambda)
                (walk-lambda (cdr expr) env))
               ;; (let ((var val) ...) body ...) or named let
               ((eq? head 'let)
                (walk-let (cdr expr) env))
               ;; (letrec ((var val) ...) body ...)
               ((eq? head 'letrec)
                (walk-letrec (cdr expr) env))
               ;; (quote ...) - skip entirely, no identifiers to resolve
               ((eq? head 'quote) (values))
               ;; (if test then else)
               ((eq? head 'if)
                (for-each (lambda (e) (walk e env)) (cdr expr)))
               ;; (begin expr ...)
               ((eq? head 'begin)
                (walk-body (cdr expr) env))
               ;; (set! var expr)
               ((eq? head 'set!)
                (when (and (pair? (cdr expr)) (symbol? (cadr expr)))
                  (unless (memq (cadr expr) env)
                    (set! unbound (cons (cadr expr) unbound))))
                (when (and (pair? (cdr expr)) (pair? (cddr expr)))
                  (walk (caddr expr) env)))
               ;; (do ((var init step) ...) (test expr ...) body ...)
               ((eq? head 'do)
                (walk-do (cdr expr) env))
               ;; (let-values (((var ...) expr) ...) body ...)
               ((eq? head 'let-values)
                (walk-let-values (cdr expr) env))
               ;; (case expr ((datum ...) body ...) ...)
               ((eq? head 'case)
                (walk-case (cdr expr) env))
               ;; (cond ...) - walk each clause
               ((eq? head 'cond)
                (for-each
                 (lambda (clause)
                   (when (pair? clause)
                     (for-each (lambda (e) (walk e env)) clause)))
                 (cdr expr)))
               ;; (and ...) (or ...)
               ((or (eq? head 'and) (eq? head 'or))
                (for-each (lambda (e) (walk e env)) (cdr expr)))
               ;; Forbidden forms - flag them and scan subforms for more forbidden heads
               ((memq head '(define-syntax syntax-case syntax-rules))
                (set! unbound (cons head unbound))
                (for-each (lambda (e)
                            (when (and (pair? e) (memq (car e) '(define-syntax syntax-case syntax-rules)))
                              (walk e env)))
                          (cdr expr)))
               ;; General application or other form
               (else
                (for-each (lambda (e) (walk e env)) expr)))))))

      ;; (define name expr) or (define (name . params) body ...)
      (define (walk-define rest env)
        (cond
          ;; (define (name params ...) body ...)
          ((and (pair? rest) (pair? (car rest)))
           (let* ((sig (car rest))
                  (name (car sig))
                  (params (cdr sig))
                  (body (cdr rest))
                  (param-syms (extract-params params))
                  (new-env (cons name (append param-syms env))))
             (for-each (lambda (e) (walk e new-env)) body)))
          ;; (define name expr)
          ((and (pair? rest) (symbol? (car rest)) (pair? (cdr rest)))
           (let ((name (car rest))
                 (val (cadr rest)))
             (walk val (cons name env))))
          (else (values))))

      ;; (lambda (params ...) body ...)
      (define (walk-lambda rest env)
        (when (and (pair? rest) (or (pair? (car rest)) (null? (car rest)) (symbol? (car rest))))
          (let* ((params (car rest))
                 (body (cdr rest))
                 (param-syms (extract-params params))
                 (new-env (append param-syms env)))
            (for-each (lambda (e) (walk e new-env)) body))))

      ;; (let ((var val) ...) body ...) or (let name ((var val) ...) body ...)
      (define (walk-let rest env)
        (cond
          ;; named let: (let name ((var val) ...) body ...)
          ((and (pair? rest) (symbol? (car rest)))
           (let* ((name (car rest))
                  (bindings (cadr rest))
                  (body (cddr rest))
                  (vars (map car bindings))
                  (vals (map cadr bindings))
                  (new-env (cons name (append vars env))))
             ;; vals are evaluated in outer env (but name is available for recursion)
             (for-each (lambda (v) (walk v env)) vals)
             (walk-body body new-env)))
          ;; regular let: (let ((var val) ...) body ...)
          ((and (pair? rest) (pair? (car rest)))
           (let* ((bindings (car rest))
                  (body (cdr rest))
                  (vars (map car bindings))
                  (vals (map cadr bindings))
                  (new-env (append vars env)))
             ;; vals are evaluated in outer env
             (for-each (lambda (v) (walk v env)) vals)
             (walk-body body new-env)))
          ;; empty let: (let () body ...)
          ((and (pair? rest) (null? (car rest)))
           (walk-body (cdr rest) env))
          (else (values))))

      ;; (letrec ((var val) ...) body ...)
      (define (walk-letrec rest env)
        (when (and (pair? rest) (or (pair? (car rest)) (null? (car rest))))
          (let* ((bindings (if (null? (car rest)) '() (car rest)))
                 (body (cdr rest))
                 (vars (map car bindings))
                 (vals (map cadr bindings))
                 ;; In letrec, all vars are in scope for all vals and body
                 (new-env (append vars env)))
            (for-each (lambda (v) (walk v new-env)) vals)
            (walk-body body new-env))))

      ;; (do ((var init step) ...) (test expr ...) body ...)
      (define (walk-do rest env)
        (when (and (pair? rest) (pair? (cdr rest)))
          (let* ((bindings (car rest))
                 (termination (cadr rest))
                 (body (cddr rest))
                 ;; Extract var names from bindings
                 (vars (map car bindings))
                 (new-env (append vars env)))
            ;; Walk init exprs in outer env
            (for-each (lambda (binding)
                        (when (and (pair? binding) (pair? (cdr binding)))
                          (walk (cadr binding) env)))
                      bindings)
            ;; Walk step exprs in new env (vars are visible)
            (for-each (lambda (binding)
                        (when (and (pair? binding) (pair? (cdr binding)) (pair? (cddr binding)))
                          (walk (caddr binding) new-env)))
                      bindings)
            ;; Walk termination clause in new env
            (when (pair? termination)
              (for-each (lambda (e) (walk e new-env)) termination))
            ;; Walk body in new env
            (for-each (lambda (e) (walk e new-env)) body))))

      ;; (let-values (((var ...) expr) ...) body ...)
      (define (walk-let-values rest env)
        (when (and (pair? rest) (or (pair? (car rest)) (null? (car rest))))
          (let* ((bindings (car rest))
                 (body (cdr rest))
                 ;; Extract all var names from formals lists
                 (vars (apply append
                             (map (lambda (binding)
                                    (if (pair? binding)
                                        (extract-params (car binding))
                                        '()))
                                  bindings)))
                 (new-env (append vars env)))
            ;; Walk value exprs in outer env
            (for-each (lambda (binding)
                        (when (and (pair? binding) (pair? (cdr binding)))
                          (walk (cadr binding) env)))
                      bindings)
            ;; Walk body in new env
            (walk-body body new-env))))

      ;; (case expr ((datum ...) body ...) ...)
      (define (walk-case rest env)
        (when (pair? rest)
          ;; Walk the key expression
          (walk (car rest) env)
          ;; Walk each clause, skipping datums
          (for-each (lambda (clause)
                      (when (pair? clause)
                        ;; First element is datum list (or 'else') - skip it
                        ;; Walk remaining elements as body expressions
                        (if (eq? (car clause) 'else)
                            (for-each (lambda (e) (walk e env)) (cdr clause))
                            (for-each (lambda (e) (walk e env)) (cdr clause)))))
                    (cdr rest))))

      ;; Walk a body (sequence of expressions) collecting top-level defines
      (define (walk-body exprs env)
        ;; First pass: collect all top-level define names
        (let* ((defined-names
                (filter symbol?
                        (map (lambda (expr)
                               (if (and (pair? expr) (eq? (car expr) 'define))
                                   (let ((rest (cdr expr)))
                                     (cond
                                       ((and (pair? rest) (pair? (car rest)))
                                        (caar rest))
                                       ((and (pair? rest) (symbol? (car rest)))
                                        (car rest))
                                       (else #f)))
                                   #f))
                             exprs)))
               (body-env (append defined-names env)))
          ;; Second pass: walk each expression with all defines in scope
          (for-each (lambda (e) (walk e body-env)) exprs)))

      ;; Extract parameter symbols from a lambda formals list
      ;; Handles: (a b c), (a b . rest), or just rest
      (define (extract-params params)
        (cond
          ((null? params) '())
          ((symbol? params) (list params))
          ((pair? params)
           (cons (car params) (extract-params (cdr params))))
          (else '())))

      ;; Walk the top-level body
      (walk-body exprs '())

      ;; Return deduplicated unbound list
      (deduplicate unbound)))

  ;; Remove duplicates from a list of symbols
  (define (deduplicate syms)
    (let loop ((remaining syms) (seen '()) (result '()))
      (if (null? remaining)
          (reverse result)
          (let ((s (car remaining)))
            (if (memq s seen)
                (loop (cdr remaining) seen result)
                (loop (cdr remaining) (cons s seen) (cons s result)))))))

  ;; Check a list of expressions against a whitelist (list of allowed symbols).
  ;; Returns a list of violation records.
  (define (check-expressions exprs whitelist)
    (let ((unbound (collect-unbound exprs)))
      (filter (lambda (v) v)
              (map (lambda (id)
                     (if (memq id whitelist)
                         #f
                         (make-wl-violation id 'unbound)))
                   unbound))))

  ;; Check source code string against a whitelist.
  (define (check-source source whitelist)
    (let ((exprs (read-all-expressions source)))
      (check-expressions exprs whitelist)))

  ;; Check a file against a whitelist file.
  ;; Returns a list of violation records.
  (define (check-file source-path whitelist-path)
    (let ((exprs (read-file source-path))
          (whitelist (load-whitelist whitelist-path)))
      (check-expressions exprs whitelist)))
)
