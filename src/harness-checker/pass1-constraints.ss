;; pass1-constraints.ss
;; Pass 1: Body-level parameter constraint inference.
;;
;; Walks lambda/define bodies and infers type constraints on parameters
;; from how they are used with known operators. For example:
;;   (+ x 1) implies x must be Number
;;   (car x) implies x must be Pair
;;   (string-append x "foo") implies x must be String
;;
;; Contradictory constraints on a parameter are reported as errors
;; at definition time (e.g., x cannot be both Number and Pair).

(library (harness-checker pass1-constraints)
  (export infer-param-constraints
          constraint-error?
          constraint-error-param
          constraint-error-constraints
          constraint-error-sources
          param-constraint?
          param-constraint-name
          param-constraint-type)
  (import (rnrs)
          (harness-checker types))

  ;; ---------------------------------------------------------------
  ;; Constraint records
  ;; ---------------------------------------------------------------

  ;; A single constraint on a parameter: (param-name . required-type)
  ;; with source expression for error reporting
  (define-record-type param-constraint
    (fields name type source))

  ;; A contradiction error: parameter has conflicting type requirements
  (define-record-type constraint-error
    (fields param         ;; symbol: the parameter name
            constraints   ;; list of types that conflict
            sources))     ;; list of source expressions

  ;; ---------------------------------------------------------------
  ;; Main entry point
  ;; ---------------------------------------------------------------

  ;; Given a list of top-level expressions and a type signature table,
  ;; infer parameter constraints for all lambda/define bodies.
  ;; Returns a pair: (param-types . errors)
  ;;   param-types: alist of (lambda-id . ((param . type) ...))
  ;;   errors: list of constraint-error records
  (define (infer-param-constraints exprs signatures)
    (let ((errors '())
          (param-types '()))

      (define (record-error! err)
        (set! errors (cons err errors)))

      ;; Look up the expected type for argument position `pos` of function `fn`
      ;; Returns #f if unknown
      (define (arg-type-for fn pos)
        (let ((sig (assq fn signatures)))
          (if (not sig)
              #f
              (let ((typ (cdr sig)))
                (cond
                  ((type-fn? typ)
                   (let ((params (type-fn-params typ)))
                     (if (< pos (length params))
                         (list-ref params pos)
                         #f)))
                  ((type-fn-variadic? typ)
                   (type-fn-variadic-param typ))
                  (else #f))))))

      ;; Collect constraints from a single expression on the given parameter set.
      ;; params: list of symbols (the lambda parameters)
      ;; Returns: alist of (param-symbol . ((type . source-expr) ...))
      (define (collect-body-constraints params body-exprs signatures)
        (let ((constraints (make-eq-hashtable)))  ;; hashtable: param -> list of (type . source)

          (define (add-constraint! param type source)
            (let ((existing (hashtable-ref constraints param '())))
              (hashtable-set! constraints param
                             (cons (cons type source) existing))))

          ;; Walk expression looking for applications of known functions
          ;; where a parameter is used as an argument
          (define (scan expr)
            (when (pair? expr)
              (let ((head (car expr)))
                (cond
                  ;; Known function call: (fn arg1 arg2 ...)
                  ((and (symbol? head) (assq head signatures))
                   (let ((args (cdr expr)))
                     (let loop ((remaining args) (pos 0))
                       (when (pair? remaining)
                         (let ((arg (car remaining)))
                           (when (and (symbol? arg) (memq arg params))
                             (let ((expected (arg-type-for head pos)))
                               (when (and expected
                                          (not (type-any? expected))
                                          (not (type-var? expected)))
                                 (add-constraint! arg expected expr)))))
                         (loop (cdr remaining) (+ pos 1)))))
                   ;; Also scan argument expressions recursively
                   (for-each scan (cdr expr)))

                  ;; Quote: skip
                  ((eq? head 'quote) (values))

                  ;; Lambda/define: don't descend into nested lambdas
                  ;; (their parameters shadow ours)
                  ((memq head '(lambda case-lambda)) (values))

                  ;; Let forms: scan init exprs but be careful about shadowing
                  ((memq head '(let let* letrec letrec*))
                   (let ((rest (cdr expr)))
                     (when (pair? rest)
                       (let ((bindings-or-name (car rest)))
                         (cond
                           ;; Named let: (let name ((var val) ...) body ...)
                           ((symbol? bindings-or-name)
                            (when (pair? (cdr rest))
                              (let ((bindings (cadr rest))
                                    (body (cddr rest)))
                                (when (pair? bindings)
                                  (for-each (lambda (b)
                                              (when (and (pair? b) (pair? (cdr b)))
                                                (scan (cadr b))))
                                            bindings))
                                ;; Check if any params are shadowed
                                (let ((bound (if (pair? bindings)
                                                 (map car bindings)
                                                 '())))
                                  (let ((unshadowed (filter (lambda (p)
                                                             (not (memq p bound)))
                                                           params)))
                                    (when (pair? unshadowed)
                                      (for-each scan body)))))))
                           ;; Regular let: (let ((var val) ...) body ...)
                           ((pair? bindings-or-name)
                            (let ((bindings bindings-or-name)
                                  (body (cdr rest)))
                              (for-each (lambda (b)
                                          (when (and (pair? b) (pair? (cdr b)))
                                            (scan (cadr b))))
                                        bindings)
                              ;; Check shadowing
                              (let ((bound (map car bindings)))
                                (let ((unshadowed (filter (lambda (p)
                                                           (not (memq p bound)))
                                                         params)))
                                  (when (pair? unshadowed)
                                    (for-each scan body))))))
                           (else (for-each scan (cdr rest))))))))

                  ;; Define: scan value but don't shadow our params
                  ((eq? head 'define)
                   (let ((rest (cdr expr)))
                     (when (pair? rest)
                       (cond
                         ;; (define (f args...) body) — skip, nested scope
                         ((pair? (car rest)) (values))
                         ;; (define x val)
                         ((and (symbol? (car rest)) (pair? (cdr rest)))
                          (scan (cadr rest)))
                         (else (values))))))

                  ;; If, cond, when, unless, begin, and, or: scan sub-exprs
                  ((memq head '(if cond when unless begin and or set!))
                   (for-each scan (cdr expr)))

                  ;; Generic: scan all sub-expressions
                  (else
                   (for-each scan expr))))))

          (for-each scan body-exprs)
          ;; Convert hashtable to alist
          (let-values (((keys vals) (hashtable-entries constraints)))
            (let loop ((i 0) (result '()))
              (if (= i (vector-length keys))
                  result
                  (loop (+ i 1)
                        (cons (cons (vector-ref keys i)
                                    (vector-ref vals i))
                              result)))))))

      ;; Check constraints for contradictions.
      ;; Two types contradict if neither is a subtype of the other
      ;; and they are both concrete (not Any/type-var).
      (define (check-contradictions param constraint-pairs)
        (let ((types (map car constraint-pairs)))
          (let loop ((remaining types) (idx 0))
            (when (pair? remaining)
              (let ((t1 (car remaining)))
                (let inner ((rest (cdr remaining)) (j (+ idx 1)))
                  (when (pair? rest)
                    (let ((t2 (car rest)))
                      (when (and (not (subtype? t1 t2))
                                 (not (subtype? t2 t1)))
                        (record-error!
                         (make-constraint-error
                          param
                          (list t1 t2)
                          (list (cdr (list-ref constraint-pairs idx))
                                (cdr (list-ref constraint-pairs j)))))))
                    (inner (cdr rest) (+ j 1)))))
              (loop (cdr remaining) (+ idx 1))))))

      ;; Process a lambda body: extract params, collect constraints, check
      ;; Returns alist of (param . resolved-type) for non-contradictory params
      (define (process-lambda params body-exprs)
        (let ((constraints (collect-body-constraints params body-exprs signatures)))
          ;; Check each parameter's constraints for contradictions
          (let ((resolved '()))
            (for-each
             (lambda (entry)
               (let ((param (car entry))
                     (type-source-pairs (cdr entry)))
                 (check-contradictions param type-source-pairs)
                 ;; If no contradiction recorded for this param, use the most specific type
                 ;; (pick first non-Any constraint as representative)
                 (let ((types (map car type-source-pairs)))
                   (when (pair? types)
                     (set! resolved
                       (cons (cons param (car types)) resolved))))))
             constraints)
            resolved)))

      ;; Walk all expressions finding lambda/define definitions
      (define (walk-top-level expr)
        (when (pair? expr)
          (let ((head (car expr)))
            (case head
              ((define)
               (let ((rest (cdr expr)))
                 (cond
                   ;; (define (f params...) body...)
                   ((and (pair? rest) (pair? (car rest)))
                    (let* ((sig (car rest))
                           (name (car sig))
                           (formals (cdr sig))
                           (params (extract-params formals))
                           (body (cdr rest)))
                      (when (pair? params)
                        (let ((resolved (process-lambda params body)))
                          (when (pair? resolved)
                            (set! param-types
                              (cons (cons name resolved) param-types)))))))
                   ;; (define name (lambda (params...) body...))
                   ((and (pair? rest) (symbol? (car rest))
                         (pair? (cdr rest)) (pair? (cadr rest))
                         (eq? (caadr rest) 'lambda))
                    (let* ((name (car rest))
                           (lam (cadr rest))
                           (formals (cadr lam))
                           (params (extract-params formals))
                           (body (cddr lam)))
                      (when (pair? params)
                        (let ((resolved (process-lambda params body)))
                          (when (pair? resolved)
                            (set! param-types
                              (cons (cons name resolved) param-types)))))))
                   (else (values)))))

              ((lambda)
               ;; Anonymous lambda at top level — track with gensym-style key
               (values))

              ((begin)
               (for-each walk-top-level (cdr expr)))

              (else (values))))))

      ;; Extract parameter symbols from formals
      (define (extract-params formals)
        (cond
          ((null? formals) '())
          ((symbol? formals) (list formals))
          ((pair? formals)
           (cons (car formals) (extract-params (cdr formals))))
          (else '())))

      ;; Run the analysis
      (for-each walk-top-level exprs)

      ;; Return results
      (cons param-types (reverse errors))))
)
