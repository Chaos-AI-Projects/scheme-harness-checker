;; type-env-builder.ss
;; Constructs per-function parameter type bindings for termination analysis
;; by merging type information from two sources:
;;
;;   1. Function signatures — maps each defined function's formal parameter
;;      names to the corresponding parameter types from its signature.
;;   2. Pass 1 constraint inference — per-function parameter type alists
;;      derived from how parameters are used with known operators.
;;
;; Priority (assq finds first match):
;;   pass1 param types > signature-derived param types
;;
;; The result is a per-function alist ((fn-name . ((param . type) ...)) ...)
;; suitable for syntactically-scoped type-env construction in the termination
;; checker — each function's parameter bindings are prepended to the global
;; type-env when analyzing that function's body.

(library (harness-checker type-env-builder)
  (export build-type-env)
  (import (rnrs)
          (harness-checker types))

  ;; Extract formal parameter names from a define form.
  ;; Returns a list of symbols or '() if not a define.
  (define (define-formals expr)
    (and (pair? expr)
         (eq? (car expr) 'define)
         (pair? (cdr expr))
         (cond
           ;; (define (f a b c) body...)
           ((pair? (cadr expr))
            (let ((sig (cadr expr)))
              (extract-params (cdr sig))))
           ;; (define f (lambda (a b c) body...))
           ((and (symbol? (cadr expr))
                 (pair? (cddr expr))
                 (pair? (caddr expr))
                 (eq? (car (caddr expr)) 'lambda)
                 (pair? (cdr (caddr expr))))
            (extract-params (cadr (caddr expr))))
           (else #f))))

  ;; Extract the function name from a define form, or #f.
  (define (define-name expr)
    (and (pair? expr)
         (eq? (car expr) 'define)
         (pair? (cdr expr))
         (cond
           ((pair? (cadr expr)) (car (cadr expr)))
           ((symbol? (cadr expr)) (cadr expr))
           (else #f))))

  ;; Extract parameter symbols from formals (handles dotted/rest params).
  (define (extract-params formals)
    (cond
      ((null? formals) '())
      ((symbol? formals) (list formals))
      ((pair? formals)
       (cons (car formals) (extract-params (cdr formals))))
      (else '())))

  ;; Extract parameter types from a function signature for given formals.
  ;; sig-type: the function's type from the signatures alist.
  ;; formals: list of parameter name symbols.
  ;; Returns alist ((param . type) ...) for parameters that have known types.
  (define (signature-param-types sig-type formals)
    (cond
      ((type-fn? sig-type)
       (let ((param-types (type-fn-params sig-type)))
         (let loop ((fs formals) (ts param-types) (acc '()))
           (if (or (null? fs) (null? ts))
               (reverse acc)
               (let ((t (car ts)))
                 (if (or (type-any? t) (type-var? t))
                     ;; Skip Any and type variables — no useful info
                     (loop (cdr fs) (cdr ts) acc)
                     (loop (cdr fs) (cdr ts)
                           (cons (cons (car fs) t) acc))))))))
      ((type-fn-variadic? sig-type)
       (let ((param-type (type-fn-variadic-param sig-type)))
         (if (or (type-any? param-type) (type-var? param-type))
             '()
             (map (lambda (f) (cons f param-type)) formals))))
      (else '())))

  ;; Collect all define forms from top-level expressions, including
  ;; those wrapped in (begin ...).
  (define (collect-defines exprs)
    (let loop ((remaining exprs) (acc '()))
      (if (null? remaining)
          (reverse acc)
          (let ((e (car remaining)))
            (cond
              ((and (pair? e) (eq? (car e) 'define))
               (loop (cdr remaining) (cons e acc)))
              ((and (pair? e) (eq? (car e) 'begin))
               (loop (cdr remaining)
                     (append (reverse (collect-defines (cdr e))) acc)))
              (else
               (loop (cdr remaining) acc)))))))

  ;; build-type-env : exprs x signatures x param-types -> per-function-param-types
  ;;
  ;; exprs      — list of top-level s-expressions (the parsed source)
  ;; signatures — alist of (fn-name . fn-type) from signature files + tool schemas
  ;; param-types — alist of (fn-name . ((param . type) ...)) from Pass 1
  ;;
  ;; Returns a per-function alist ((fn-name . ((param . type) ...)) ...) with
  ;; merged parameter types for each defined function.  Pass 1 types have
  ;; higher priority than signature-derived types (via assq first-match when
  ;; the per-function bindings are prepended to the global type-env).
  (define (build-type-env exprs signatures param-types)
    (let* ((defines (collect-defines exprs)))
      (let loop ((defs defines) (acc '()))
        (if (null? defs)
            (reverse acc)
            (let* ((d (car defs))
                   (name (define-name d))
                   (formals (define-formals d)))
              (if (and name formals (pair? formals))
                  (let* (;; Signature-derived param types for this function
                         (sig (assq name signatures))
                         (sig-derived (if sig
                                         (signature-param-types (cdr sig) formals)
                                         '()))
                         ;; Pass 1 param types for this function (filter out Any)
                         (p1 (assq name param-types))
                         (p1-bindings (if p1
                                         (filter (lambda (b) (not (type-any? (cdr b))))
                                                 (cdr p1))
                                         '()))
                         ;; Merge: p1 first (higher priority via assq first-match)
                         (merged (append p1-bindings sig-derived)))
                    (if (null? merged)
                        (loop (cdr defs) acc)
                        (loop (cdr defs) (cons (cons name merged) acc))))
                  (loop (cdr defs) acc))))))))
