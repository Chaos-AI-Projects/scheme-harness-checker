;; type-infer.ss
;; Pass 2: Forward type inference and call-site checking.
;;
;; Single forward pass over the AST:
;; - Infers types of expressions from literals, known operators, and bindings
;; - Checks call sites against function signatures (arity + argument types)
;; - Uses Pass 1 results for user-defined function parameter types

(library (harness-checker type-infer)
  (export check-types
          type-error?
          type-error-kind
          type-error-expr
          type-error-expected
          type-error-actual
          type-error-function
          type-error-position)
  (import (rnrs)
          (harness-checker types))

  ;; ---------------------------------------------------------------
  ;; Type error records
  ;; ---------------------------------------------------------------
  (define-record-type type-error
    (fields kind       ;; 'arity | 'type-mismatch
            expr       ;; the offending expression
            expected   ;; expected type or arity range (string)
            actual     ;; actual type or arg count (string)
            function   ;; function name (symbol or #f)
            position)) ;; argument position (integer or #f)

  ;; ---------------------------------------------------------------
  ;; Main entry point
  ;; ---------------------------------------------------------------

  ;; Check types in a list of expressions.
  ;; signatures: alist of (symbol . type) from type-signatures.scm
  ;; param-types: alist of (fn-name . ((param . type) ...)) from Pass 1
  ;; Returns: list of type-error records
  (define (check-types exprs signatures param-types)
    (let ((errors '()))

      (define (record-error! err)
        (set! errors (cons err errors)))

      ;; Type environment: alist of (symbol . type)
      ;; Lookup with fallback to Any
      (define (env-lookup sym env)
        (let ((entry (assq sym env)))
          (if entry (cdr entry) type:any)))

      ;; ---------------------------------------------------------------
      ;; Type inference for expressions
      ;; ---------------------------------------------------------------

      ;; Infer the type of an expression in the given environment.
      ;; Also performs call-site checking as a side effect.
      (define (infer expr env)
        (cond
          ;; Literals
          ((number? expr) type:number)
          ((string? expr) type:string)
          ((boolean? expr) type:bool)
          ((char? expr) type:char)
          ((null? expr) type:null)

          ;; Symbols: look up in environment, then signatures
          ((symbol? expr)
           (let ((env-type (env-lookup expr env)))
             (if (type-any? env-type)
                 ;; Check if it's a known function from signatures
                 (let ((sig (assq expr signatures)))
                   (if sig (cdr sig) type:any))
                 env-type)))

          ;; Pairs (applications and special forms)
          ((pair? expr)
           (let ((head (car expr)))
             (cond
               ;; Quote
               ((eq? head 'quote)
                (if (pair? (cdr expr))
                    (infer-quoted (cadr expr))
                    type:any))

               ;; Lambda
               ((eq? head 'lambda)
                (infer-lambda expr env))

               ;; Define
               ((eq? head 'define)
                (infer-define expr env)
                type:void)

               ;; If
               ((eq? head 'if)
                (infer-if expr env))

               ;; Let forms
               ((memq head '(let let* letrec letrec*))
                (infer-let expr env))

               ;; Begin
               ((eq? head 'begin)
                (infer-begin expr env))

               ;; Set!
               ((eq? head 'set!)
                (when (and (pair? (cdr expr)) (pair? (cddr expr)))
                  (infer (caddr expr) env))
                type:void)

               ;; Cond
               ((eq? head 'cond)
                (infer-cond expr env))

               ;; When/unless
               ((memq head '(when unless))
                (if (pair? (cdr expr))
                    (begin
                      (infer (cadr expr) env)
                      (let ((body (cddr expr)))
                        (if (pair? body)
                            (let loop ((remaining body))
                              (if (null? (cdr remaining))
                                  (infer (car remaining) env)
                                  (begin (infer (car remaining) env)
                                         (loop (cdr remaining)))))
                            type:void)))
                    type:void))

               ;; And/or
               ((memq head '(and or))
                (let ((sub-exprs (cdr expr)))
                  (if (null? sub-exprs)
                      type:bool
                      (let loop ((remaining sub-exprs))
                        (let ((t (infer (car remaining) env)))
                          (if (null? (cdr remaining))
                              t
                              (loop (cdr remaining))))))))

               ;; Case
               ((eq? head 'case)
                (when (pair? (cdr expr))
                  (infer (cadr expr) env))
                type:any)

               ;; Do
               ((eq? head 'do)
                type:any)

               ;; Function application
               ((symbol? head)
                (infer-application head (cdr expr) expr env))

               ;; Application with expression in head position
               (else
                (infer head env)
                (for-each (lambda (arg) (infer arg env)) (cdr expr))
                type:any))))

          ;; Vectors, other literals
          (else type:any)))

      ;; ---------------------------------------------------------------
      ;; Infer type of quoted data
      ;; ---------------------------------------------------------------
      (define (infer-quoted datum)
        (cond
          ((number? datum) type:number)
          ((string? datum) type:string)
          ((boolean? datum) type:bool)
          ((char? datum) type:char)
          ((symbol? datum) type:symbol)
          ((null? datum) type:null)
          ((pair? datum)
           ;; Try to determine if it's a proper list
           (if (list? datum)
               (make-type-list (infer-quoted-list-elem datum))
               (make-type-pair (infer-quoted (car datum))
                               (infer-quoted (cdr datum)))))
          (else type:any)))

      (define (infer-quoted-list-elem datum)
        (if (null? datum)
            type:any
            (let ((first-type (infer-quoted (car datum))))
              ;; Check if all elements have same type
              (if (for-all (lambda (e) (type=? (infer-quoted e) first-type))
                           (cdr datum))
                  first-type
                  type:any))))

      ;; ---------------------------------------------------------------
      ;; Lambda inference
      ;; ---------------------------------------------------------------
      (define (infer-lambda expr env)
        (let* ((formals (cadr expr))
               (body (cddr expr))
               (params (extract-params formals))
               (param-types-local
                (map (lambda (p) (cons p type:any)) params))
               (new-env (append param-types-local env)))
          ;; Infer body in new env
          (let ((return-type (infer-body body new-env)))
            (make-type-fn (map (lambda (_) type:any) params) return-type))))

      ;; ---------------------------------------------------------------
      ;; Define
      ;; ---------------------------------------------------------------
      (define (infer-define expr env)
        (let ((rest (cdr expr)))
          (when (pair? rest)
            (cond
              ;; (define (f args...) body...)
              ((pair? (car rest))
               (values))  ;; handled at top-level
              ;; (define x val)
              ((and (symbol? (car rest)) (pair? (cdr rest)))
               (infer (cadr rest) env))
              (else (values))))))

      ;; ---------------------------------------------------------------
      ;; If
      ;; ---------------------------------------------------------------
      (define (infer-if expr env)
        (let ((parts (cdr expr)))
          (when (pair? parts)
            (infer (car parts) env))  ;; test
          (if (and (pair? parts) (pair? (cdr parts)))
              (let ((then-type (infer (cadr parts) env)))
                (if (pair? (cddr parts))
                    (let ((else-type (infer (caddr parts) env)))
                      (simplify-union (list then-type else-type)))
                    then-type))
              type:any)))

      ;; ---------------------------------------------------------------
      ;; Let forms
      ;; ---------------------------------------------------------------
      (define (infer-let expr env)
        (let* ((head (car expr))
               (rest (cdr expr)))
          (if (not (pair? rest))
              type:any
              (cond
                ;; Named let: (let name ((var val) ...) body...)
                ((and (eq? head 'let) (symbol? (car rest)))
                 (let ((bindings (if (pair? (cdr rest)) (cadr rest) '()))
                       (body (if (pair? (cdr rest)) (cddr rest) '())))
                   (let* ((bind-env
                           (if (pair? bindings)
                               (map (lambda (b)
                                      (cons (car b)
                                            (if (pair? (cdr b))
                                                (infer (cadr b) env)
                                                type:any)))
                                    bindings)
                               '()))
                          (new-env (append bind-env env)))
                     (infer-body body new-env))))

                ;; Regular let/letrec/let*
                (else
                 (let ((bindings (car rest))
                       (body (cdr rest)))
                   (if (not (pair? bindings))
                       (infer-body body env)
                       (let* ((bind-env
                               (cond
                                 ((eq? head 'let*)
                                  ;; Sequential binding
                                  (let loop ((remaining bindings) (acc-env env))
                                    (if (null? remaining)
                                        acc-env
                                        (let* ((b (car remaining))
                                               (var (car b))
                                               (val-type (if (pair? (cdr b))
                                                             (infer (cadr b) acc-env)
                                                             type:any)))
                                          (loop (cdr remaining)
                                                (cons (cons var val-type) acc-env))))))
                                 ((memq head '(letrec letrec*))
                                  ;; All names visible in init exprs
                                  (let ((pre-env
                                         (append
                                          (map (lambda (b) (cons (car b) type:any))
                                               bindings)
                                          env)))
                                    (append
                                     (map (lambda (b)
                                            (cons (car b)
                                                  (if (pair? (cdr b))
                                                      (infer (cadr b) pre-env)
                                                      type:any)))
                                          bindings)
                                     env)))
                                 (else
                                  ;; Regular let: init exprs in outer env
                                  (append
                                   (map (lambda (b)
                                          (cons (car b)
                                                (if (pair? (cdr b))
                                                    (infer (cadr b) env)
                                                    type:any)))
                                        bindings)
                                   env))))
                              (new-env (if (eq? head 'let*)
                                           bind-env
                                           bind-env)))
                         (infer-body body new-env)))))))))

      ;; ---------------------------------------------------------------
      ;; Begin
      ;; ---------------------------------------------------------------
      (define (infer-begin expr env)
        (infer-body (cdr expr) env))

      ;; ---------------------------------------------------------------
      ;; Cond
      ;; ---------------------------------------------------------------
      (define (infer-cond expr env)
        (let ((clauses (cdr expr)))
          (if (null? clauses)
              type:void
              (let loop ((remaining clauses) (types '()))
                (if (null? remaining)
                    (if (null? types)
                        type:void
                        (simplify-union types))
                    (let ((clause (car remaining)))
                      (if (pair? clause)
                          (begin
                            ;; Infer test (unless it's 'else')
                            (unless (eq? (car clause) 'else)
                              (infer (car clause) env))
                            ;; Infer body exprs
                            (let ((body-type (if (pair? (cdr clause))
                                                 (infer-body (cdr clause) env)
                                                 type:void)))
                              (loop (cdr remaining) (cons body-type types))))
                          (loop (cdr remaining) types))))))))

      ;; ---------------------------------------------------------------
      ;; Function application checking
      ;; ---------------------------------------------------------------
      (define (infer-application fn args call-expr env)
        (let ((arg-types (map (lambda (a) (infer a env)) args))
              (argc (length args)))

          ;; Look up function signature
          (let ((sig-entry (assq fn signatures)))
            (if sig-entry
                (let ((fn-type (cdr sig-entry)))
                  (cond
                    ;; Fixed-arity function
                    ((type-fn? fn-type)
                     (let ((expected-params (type-fn-params fn-type))
                           (return-type (type-fn-return fn-type)))
                       ;; Check arity
                       (let ((expected-arity (length expected-params)))
                         (unless (= argc expected-arity)
                           (record-error!
                            (make-type-error
                             'arity
                             call-expr
                             (number->string expected-arity)
                             (number->string argc)
                             fn
                             #f))))
                       ;; Check argument types
                       (let loop ((params expected-params)
                                  (actuals arg-types)
                                  (pos 0))
                         (when (and (pair? params) (pair? actuals))
                           (let ((expected (car params))
                                 (actual (car actuals)))
                             (unless (or (type-any? expected)
                                         (type-any? actual)
                                         (type-var? expected)
                                         (type-var? actual)
                                         (subtype? actual expected))
                               (record-error!
                                (make-type-error
                                 'type-mismatch
                                 call-expr
                                 (type->string expected)
                                 (type->string actual)
                                 fn
                                 (+ pos 1)))))
                           (loop (cdr params) (cdr actuals) (+ pos 1))))
                       ;; Return type
                       (if (type-var? return-type)
                           type:any
                           return-type)))

                    ;; Variadic function
                    ((type-fn-variadic? fn-type)
                     (let ((param-type (type-fn-variadic-param fn-type))
                           (return-type (type-fn-variadic-return fn-type))
                           (min-arity (type-fn-variadic-min-arity fn-type)))
                       ;; Check minimum arity
                       (when (< argc min-arity)
                         (record-error!
                          (make-type-error
                           'arity
                           call-expr
                           (string-append (number->string min-arity) "+")
                           (number->string argc)
                           fn
                           #f)))
                       ;; Check each argument type
                       (unless (or (type-any? param-type) (type-var? param-type))
                         (let loop ((actuals arg-types) (pos 0))
                           (when (pair? actuals)
                             (let ((actual (car actuals)))
                               (unless (or (type-any? actual)
                                           (type-var? actual)
                                           (subtype? actual param-type))
                                 (record-error!
                                  (make-type-error
                                   'type-mismatch
                                   call-expr
                                   (type->string param-type)
                                   (type->string actual)
                                   fn
                                   (+ pos 1)))))
                             (loop (cdr actuals) (+ pos 1)))))
                       ;; Return type
                       (if (type-var? return-type)
                           type:any
                           return-type)))

                    (else type:any)))

                ;; Not in signatures — check if it's a user-defined function
                ;; with Pass 1 constraints
                (let ((user-fn (assq fn param-types)))
                  (if user-fn
                      (let ((param-constraints (cdr user-fn)))
                        ;; Check argument types against inferred constraints
                        (let loop ((constraints param-constraints)
                                   (actuals arg-types)
                                   (pos 0))
                          (when (and (pair? constraints) (pair? actuals))
                            (let ((expected (cdar constraints))
                                  (actual (car actuals)))
                              (unless (or (type-any? expected)
                                          (type-any? actual)
                                          (type-var? expected)
                                          (type-var? actual)
                                          (subtype? actual expected))
                                (record-error!
                                 (make-type-error
                                  'type-mismatch
                                  call-expr
                                  (type->string expected)
                                  (type->string actual)
                                  fn
                                  (+ pos 1)))))
                            (loop (cdr constraints) (cdr actuals) (+ pos 1))))
                        type:any)
                      ;; Completely unknown function
                      type:any))))))

      ;; ---------------------------------------------------------------
      ;; Helpers
      ;; ---------------------------------------------------------------

      ;; Infer type of a body (sequence of expressions), returning last type
      (define (infer-body exprs env)
        (if (null? exprs)
            type:void
            (let loop ((remaining exprs))
              (if (null? (cdr remaining))
                  (infer (car remaining) env)
                  (begin
                    (infer (car remaining) env)
                    (loop (cdr remaining)))))))

      ;; Extract parameter symbols from formals
      (define (extract-params formals)
        (cond
          ((null? formals) '())
          ((symbol? formals) (list formals))
          ((pair? formals)
           (cons (car formals) (extract-params (cdr formals))))
          (else '())))

      ;; ---------------------------------------------------------------
      ;; Run the checker
      ;; ---------------------------------------------------------------

      ;; Build initial type environment from top-level defines
      (define (build-top-env exprs)
        (let loop ((remaining exprs) (env '()))
          (if (null? remaining)
              env
              (let ((expr (car remaining)))
                (if (and (pair? expr) (eq? (car expr) 'define))
                    (let ((rest (cdr expr)))
                      (cond
                        ;; (define (f args...) body...)
                        ((and (pair? rest) (pair? (car rest)))
                         (let ((name (caar rest)))
                           (loop (cdr remaining)
                                 (cons (cons name type:any) env))))
                        ;; (define x val)
                        ((and (pair? rest) (symbol? (car rest)))
                         (let ((name (car rest)))
                           (loop (cdr remaining)
                                 (cons (cons name type:any) env))))
                        (else (loop (cdr remaining) env))))
                    (loop (cdr remaining) env))))))

      (let ((top-env (build-top-env exprs)))
        ;; Now infer each top-level expression
        (for-each (lambda (expr) (infer expr top-env)) exprs))

      ;; Return collected errors
      (reverse errors)))
)
