;; peg-walker.ss
;; PEG-based s-expression tree walker for whitelist checking.
;;
;; Uses packrat PEG patterns to match Scheme form structures,
;; with a fused single-pass design that carries the lexical
;; environment as an inherited attribute.
;;
;; Architecture (from issue #248):
;;   Pass 0: Forbidden form detection (PEG match on heads)
;;   Pass 1+2 fused: Walk tree with PEG rules, threading env,
;;                    collecting unbound references
;;   Pass 3+4: Set operations (pure Scheme, no PEG)

(library (harness-checker peg-walker)
  (export peg-collect-unbound)
  (import (rnrs)
          (packrat-ext packrat))

  ;; ---------------------------------------------------------------
  ;; Token encoding for s-expression elements
  ;; ---------------------------------------------------------------
  ;; Each element of an s-expression list becomes a packrat token
  ;; (kind . value):
  ;;   symbol  → (the-symbol . the-symbol)   — kind IS the symbol
  ;;   pair    → (#\L . the-pair)            — #\L marks a list/pair
  ;;   other   → (#\A . the-value)           — #\A marks an atom

  (define (sexpr-token elem)
    (cond
      ((symbol? elem) (cons elem elem))
      ((pair? elem)   (cons #\L elem))
      (else           (cons #\A elem))))

  ;; Convert a list of s-expression elements to a packrat token generator
  (define (list->generator elems)
    (let ((remaining elems))
      (lambda ()
        (if (null? remaining)
            (values #f #f)
            (let ((elem (car remaining)))
              (set! remaining (cdr remaining))
              (values #f (sexpr-token elem)))))))

  ;; Parse a list's elements with the given packrat parser
  (define (parse-list-elements parser elems)
    (let ((results (base-generator->results (list->generator elems))))
      (parser results)))

  ;; ---------------------------------------------------------------
  ;; Token-kind predicates for PEG rules
  ;; ---------------------------------------------------------------
  (define (list-kind? k) (eqv? k #\L))
  (define (any-kind? k) (or (symbol? k) (eqv? k #\L) (eqv? k #\A)))

  ;; ---------------------------------------------------------------
  ;; PEG grammar for form recognition
  ;; ---------------------------------------------------------------
  ;; The grammar matches the head of a form and extracts components.
  ;; Returns a tagged list describing the form type and its parts.
  ;;
  ;; Semantic values:
  ;;   (define-fn <signature> <body-exprs>)
  ;;   (define-var <name> <val>)
  ;;   (lambda-form <formals> <body-exprs>)
  ;;   (let-form <bindings> <body-exprs>)
  ;;   (named-let <name> <bindings> <body-exprs>)
  ;;   (letrec-form <bindings> <body-exprs>)
  ;;   (let*-form <bindings> <body-exprs>)
  ;;   (case-lambda-form <clauses>)
  ;;   (do-form <bindings> <termination> <body-exprs>)
  ;;   (let-values-form <bindings> <body-exprs>)
  ;;   (case-form <key> <clauses>)
  ;;   (guard-form <guard-clause> <body-exprs>)
  ;;   (parameterize-form <bindings> <body-exprs>)
  ;;   (set!-form <var-or-expr> <val>)
  ;;   (quote-form)
  ;;   (begin-form <body-exprs>)
  ;;   (if-form <exprs>)
  ;;   (cond-form <clauses>)
  ;;   (when-form <exprs>)
  ;;   (unless-form <exprs>)
  ;;   (and-form <exprs>)
  ;;   (or-form <exprs>)
  ;;   (forbidden <head> <rest>)
  ;;   (generic <all-elems>)

  (define form-parser
    (packrat-parser
     form

     (form
      ;; (define (name . params) body ...)
      (('define sig <- (? list-kind?) body <- rest-elems)
       (list 'define-fn sig body))
      ;; (define name expr)
      (('define name <- (? symbol?) val <- (? any-kind?))
       (list 'define-var name val))
      ;; (define name) — no value
      (('define name <- (? symbol?))
       (list 'define-var name #f))

      ;; (lambda formals body ...)
      (('lambda formals <- (? any-kind?) body <- rest-elems)
       (list 'lambda-form formals body))

      ;; (let name ((var val) ...) body ...) — named let
      (('let name <- (? symbol?) bindings <- (? any-kind?) body <- rest-elems)
       (list 'named-let name bindings body))
      ;; (let ((var val) ...) body ...)
      (('let bindings <- (? any-kind?) body <- rest-elems)
       (list 'let-form bindings body))

      ;; (letrec ((var val) ...) body ...)
      (('letrec bindings <- (? any-kind?) body <- rest-elems)
       (list 'letrec-form bindings body))

      ;; (letrec* ((var val) ...) body ...)
      (('letrec* bindings <- (? any-kind?) body <- rest-elems)
       (list 'letrec-form bindings body))

      ;; (let* ((var val) ...) body ...)
      (('let* bindings <- (? any-kind?) body <- rest-elems)
       (list 'let*-form bindings body))

      ;; (case-lambda clauses ...)
      (('case-lambda clauses <- rest-elems)
       (list 'case-lambda-form clauses))

      ;; (do ((var init step) ...) (test expr ...) body ...)
      (('do bindings <- (? any-kind?) termination <- (? any-kind?) body <- rest-elems)
       (list 'do-form bindings termination body))

      ;; (let-values (((vars ...) expr) ...) body ...)
      (('let-values bindings <- (? any-kind?) body <- rest-elems)
       (list 'let-values-form bindings body))

      ;; (case expr clause ...)
      (('case key <- (? any-kind?) clauses <- rest-elems)
       (list 'case-form key clauses))

      ;; (guard (var clause ...) body ...)
      (('guard guard-clause <- (? any-kind?) body <- rest-elems)
       (list 'guard-form guard-clause body))

      ;; (parameterize ((param val) ...) body ...)
      (('parameterize bindings <- (? any-kind?) body <- rest-elems)
       (list 'parameterize-form bindings body))

      ;; (set! var expr)
      (('set! target <- (? any-kind?) val <- (? any-kind?))
       (list 'set!-form target val))

      ;; (quote ...) — skip entirely
      (('quote) (list 'quote-form))
      (('quote datum <- (? any-kind?)) (list 'quote-form))

      ;; (begin expr ...)
      (('begin body <- rest-elems)
       (list 'begin-form body))

      ;; (if test then else)
      (('if exprs <- rest-elems)
       (list 'if-form exprs))

      ;; (cond clause ...)
      (('cond clauses <- rest-elems)
       (list 'cond-form clauses))

      ;; (when test body ...)
      (('when exprs <- rest-elems)
       (list 'when-form exprs))

      ;; (unless test body ...)
      (('unless exprs <- rest-elems)
       (list 'unless-form exprs))

      ;; (and expr ...) / (or expr ...)
      (('and exprs <- rest-elems)
       (list 'and-form exprs))
      (('or exprs <- rest-elems)
       (list 'or-form exprs))

      ;; Forbidden forms
      (('define-syntax rest <- rest-elems)
       (list 'forbidden 'define-syntax rest))
      (('syntax-case rest <- rest-elems)
       (list 'forbidden 'syntax-case rest))
      (('syntax-rules rest <- rest-elems)
       (list 'forbidden 'syntax-rules rest))

      ;; Generic form — collect all elements
      ((elems <- rest-elems)
       (list 'generic elems)))

     ;; Collect remaining elements into a list
     (rest-elems
      ((e <- (? any-kind?) more <- rest-elems) (cons e more))
      (() '()))))

  ;; ---------------------------------------------------------------
  ;; Parse a list form and return its tagged structure
  ;; ---------------------------------------------------------------
  (define (classify-form elems)
    (let ((result (parse-list-elements form-parser elems)))
      (if (parse-result-successful? result)
          (parse-result-semantic-value result)
          ;; Fallback: treat as generic application
          (list 'generic elems))))

  ;; ---------------------------------------------------------------
  ;; Fused walker: threads environment, collects unbound identifiers
  ;; ---------------------------------------------------------------

  ;; Main entry point: collect all unbound identifiers from expressions.
  ;; Returns a deduplicated list of unbound symbols.
  (define (peg-collect-unbound exprs)
    (let ((unbound '()))

      ;; Record an unbound reference
      (define (record-unbound! sym)
        (set! unbound (cons sym unbound)))

      ;; Walk a single expression with the given environment
      (define (walk expr env)
        (cond
          ((symbol? expr)
           (unless (memq expr env)
             (record-unbound! expr)))
          ((not (pair? expr)) (values))
          (else
           (let ((form-desc (classify-form expr)))
             (dispatch form-desc env)))))

      ;; Dispatch on the classified form
      (define (dispatch form-desc env)
        (let ((tag (car form-desc)))
          (case tag
            ((define-fn)
             (let* ((sig (cadr form-desc))
                    (body-exprs (caddr form-desc))
                    (name (car sig))
                    (params (cdr sig))
                    (param-syms (extract-params params))
                    (new-env (cons name (append param-syms env))))
               (walk-body body-exprs new-env)))

            ((define-var)
             (let ((name (cadr form-desc))
                   (val (caddr form-desc)))
               (when val
                 (walk val (cons name env)))))

            ((lambda-form)
             (let* ((formals (cadr form-desc))
                    (body-exprs (caddr form-desc))
                    (param-syms (extract-params formals))
                    (new-env (append param-syms env)))
               (walk-body body-exprs new-env)))

            ((named-let)
             (let* ((name (cadr form-desc))
                    (bindings (caddr form-desc))
                    (body-exprs (cadddr form-desc))
                    (vars (if (or (null? bindings) (not (pair? bindings))) '() (map car bindings)))
                    (vals (if (or (null? bindings) (not (pair? bindings))) '() (map cadr bindings)))
                    (new-env (cons name (append vars env))))
               (for-each (lambda (v) (walk v env)) vals)
               (walk-body body-exprs new-env)))

            ((let-form)
             (let* ((bindings (cadr form-desc))
                    (body-exprs (caddr form-desc)))
               (cond
                 ((or (null? bindings) (not (pair? bindings)))
                  (walk-body body-exprs env))
                 (else
                  (let* ((vars (map car bindings))
                         (vals (map cadr bindings))
                         (new-env (append vars env)))
                    (for-each (lambda (v) (walk v env)) vals)
                    (walk-body body-exprs new-env))))))

            ((letrec-form)
             (let* ((bindings (cadr form-desc))
                    (body-exprs (caddr form-desc)))
               (if (or (null? bindings) (not (pair? bindings)))
                   (walk-body body-exprs env)
                   (let* ((vars (map car bindings))
                          (vals (map cadr bindings))
                          (new-env (append vars env)))
                     (for-each (lambda (v) (walk v new-env)) vals)
                     (walk-body body-exprs new-env)))))

            ((let*-form)
             (let* ((bindings (cadr form-desc))
                    (body-exprs (caddr form-desc)))
               (if (or (null? bindings) (not (pair? bindings)))
                   (walk-body body-exprs env)
                   (let loop ((remaining bindings) (current-env env))
                     (if (null? remaining)
                         (walk-body body-exprs current-env)
                         (let ((binding (car remaining)))
                           (when (and (pair? binding) (pair? (cdr binding)))
                             (walk (cadr binding) current-env))
                           (let ((var (if (pair? binding) (car binding) binding)))
                             (loop (cdr remaining) (cons var current-env)))))))))

            ((case-lambda-form)
             (let ((clauses (cadr form-desc)))
               (for-each
                (lambda (clause)
                  (when (and (pair? clause)
                             (or (pair? (car clause))
                                 (null? (car clause))
                                 (symbol? (car clause))))
                    (let* ((params (car clause))
                           (body (cdr clause))
                           (param-syms (extract-params params))
                           (new-env (append param-syms env)))
                      (walk-body body new-env))))
                clauses)))

            ((do-form)
             (let* ((bindings (cadr form-desc))
                    (termination (caddr form-desc))
                    (body-exprs (cadddr form-desc))
                    (vars (if (or (null? bindings) (not (pair? bindings))) '() (map car bindings)))
                    (new-env (append vars env)))
               ;; Walk init exprs in outer env
               (when (pair? bindings)
                 (for-each (lambda (binding)
                             (when (and (pair? binding) (pair? (cdr binding)))
                               (walk (cadr binding) env)))
                           bindings))
               ;; Walk step exprs in new env
               (when (pair? bindings)
                 (for-each (lambda (binding)
                             (when (and (pair? binding) (pair? (cdr binding)) (pair? (cddr binding)))
                               (walk (caddr binding) new-env)))
                           bindings))
               ;; Walk termination in new env
               (when (pair? termination)
                 (for-each (lambda (e) (walk e new-env)) termination))
               ;; Walk body in new env
               (for-each (lambda (e) (walk e new-env)) body-exprs)))

            ((let-values-form)
             (let* ((bindings (cadr form-desc))
                    (body-exprs (caddr form-desc)))
               (if (or (null? bindings) (not (pair? bindings)))
                   (walk-body body-exprs env)
                   (let* ((vars (apply append
                                       (map (lambda (binding)
                                              (if (pair? binding)
                                                  (extract-params (car binding))
                                                  '()))
                                            bindings)))
                          (new-env (append vars env)))
                     (for-each (lambda (binding)
                                 (when (and (pair? binding) (pair? (cdr binding)))
                                   (walk (cadr binding) env)))
                               bindings)
                     (walk-body body-exprs new-env)))))

            ((case-form)
             (let ((key (cadr form-desc))
                   (clauses (caddr form-desc)))
               (walk key env)
               (for-each (lambda (clause)
                           (when (pair? clause)
                             (if (eq? (car clause) 'else)
                                 (for-each (lambda (e) (walk e env)) (cdr clause))
                                 (for-each (lambda (e) (walk e env)) (cdr clause)))))
                         clauses)))

            ((guard-form)
             (let* ((guard-clause (cadr form-desc))
                    (body-exprs (caddr form-desc))
                    (var (car guard-clause))
                    (clauses (cdr guard-clause))
                    (new-env (cons var env)))
               (for-each
                (lambda (clause)
                  (when (pair? clause)
                    (if (eq? (car clause) 'else)
                        (for-each (lambda (e) (walk e new-env)) (cdr clause))
                        (for-each (lambda (e) (walk e new-env)) clause))))
                clauses)
               (for-each (lambda (e) (walk e env)) body-exprs)))

            ((parameterize-form)
             (let* ((bindings (cadr form-desc))
                    (body-exprs (caddr form-desc)))
               (when (pair? bindings)
                 (for-each (lambda (binding)
                             (when (pair? binding)
                               (for-each (lambda (e) (walk e env)) binding)))
                           bindings))
               (walk-body body-exprs env)))

            ((set!-form)
             (let ((target (cadr form-desc))
                   (val (caddr form-desc)))
               (when (symbol? target)
                 (unless (memq target env)
                   (record-unbound! target)))
               (walk val env)))

            ((quote-form) (values))

            ((begin-form)
             (walk-body (cadr form-desc) env))

            ((if-form when-form unless-form and-form or-form)
             (for-each (lambda (e) (walk e env)) (cadr form-desc)))

            ((cond-form)
             (for-each
              (lambda (clause)
                (when (pair? clause)
                  (for-each (lambda (e) (walk e env)) clause)))
              (cadr form-desc)))

            ((forbidden)
             (let ((head (cadr form-desc))
                   (rest (caddr form-desc)))
               (record-unbound! head)
               ;; Scan subforms for more forbidden heads
               (for-each (lambda (e)
                           (when (and (pair? e)
                                      (memq (car e) '(define-syntax syntax-case syntax-rules)))
                             (walk e env)))
                         rest)))

            ((generic)
             (for-each (lambda (e) (walk e env)) (cadr form-desc))))))

      ;; Walk a body collecting top-level defines for mutual visibility
      (define (walk-body exprs env)
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
          (for-each (lambda (e) (walk e body-env)) exprs)))

      ;; Extract parameter symbols from formals
      (define (extract-params params)
        (cond
          ((null? params) '())
          ((symbol? params) (list params))
          ((pair? params)
           (cons (car params) (extract-params (cdr params))))
          (else '())))

      ;; Run the walker
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
)
