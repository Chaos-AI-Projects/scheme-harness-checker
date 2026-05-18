;; termination.ss
;; Termination analysis pass for the harness checker.
;; Detects programs that may not terminate (infinite loops / unbounded recursion).
;;
;; Phase 1 (scaffolding): stub returning empty list for all inputs.
;; Phase 2 (call graph): build directed call graph from top-level definitions
;;   and identify strongly connected components (SCCs) for recursion analysis.
;; Phase 3 (do-form analysis): analyze do-loop constructs for termination by
;;   verifying exit conditions and step expressions.
;; Phase 4 (named-let analysis): analyze named-let loops for termination by
;;   checking for decreasing arguments and base cases.
;; Phase 5 (direct recursion): analyze directly recursive functions for
;;   decreasing arguments and base cases using call graph SCCs.
;; Phase 6 (mutual recursion): analyze mutually recursive function groups
;;   (multi-node SCCs) for decreasing arguments across all call edges.

(library (harness-checker termination)
  (export check-termination
          make-termination-violation
          termination-violation?
          termination-violation-kind
          termination-violation-function
          termination-violation-expr
          termination-violation-reason
          ;; Phase 2: call graph construction
          build-call-graph
          call-graph-edges
          extract-definitions
          tarjan-scc
          ;; Phase 3: do-form analysis
          analyze-do-forms
          ;; Phase 4: named-let analysis
          analyze-named-let-forms
          ;; Phase 5: direct recursion analysis
          analyze-direct-recursion
          extract-formals
          ;; Phase 6: mutual recursion analysis
          analyze-mutual-recursion
          ;; Collection HOF whitelist
          collection-hof?
          ;; Type-env lookup
          type-env-lookup)
  (import (rnrs)
          (harness-checker types))

  ;; Record type for termination violations.
  ;; Fields:
  ;;   kind     - symbol: 'infinite-loop | 'unbounded-loop | 'unbounded-recursion | 'no-base-case | 'no-exit-condition
  ;;   function - symbol or #f: name of the function/construct involved
  ;;   expr     - the offending s-expression
  ;;   reason   - string: human-readable explanation
  (define-record-type termination-violation
    (fields kind function expr reason))

  ;; ---------------------------------------------------------------
  ;; Utility
  ;; ---------------------------------------------------------------

  (define (deduplicate syms)
    (let loop ((remaining syms) (seen '()) (result '()))
      (if (null? remaining)
          (reverse result)
          (let ((s (car remaining)))
            (if (memq s seen)
                (loop (cdr remaining) seen result)
                (loop (cdr remaining) (cons s seen) (cons s result)))))))

  ;; ---------------------------------------------------------------
  ;; Type environment lookup
  ;; ---------------------------------------------------------------

  ;; Look up a variable's type in the type environment.
  ;; type-env is an alist ((symbol . type) ...).
  ;; Returns the type or #f if not found.
  (define (type-env-lookup type-env var)
    (let ((entry (assq var type-env)))
      (and entry (cdr entry))))

  ;; Check if a type contains Null as a union member.
  ;; Used to detect nullable self-referential record fields (linked-list patterns).
  (define (type-contains-null? t)
    (cond
      ((type-base? t) (eq? (type-base-name t) 'Null))
      ((type-union? t)
       (exists type-contains-null? (type-union-members t)))
      (else #f)))

  ;; ---------------------------------------------------------------
  ;; Collection HOF whitelist
  ;; ---------------------------------------------------------------

  ;; Hardcoded list of known-terminating higher-order functions that
  ;; iterate over finite collections. These are R6RS/Chez built-ins.
  ;; Since set-cdr! is not in the harness whitelist, inputs are always
  ;; proper lists, so these functions provably terminate.
  (define collection-hof-names
    '(map for-each filter remove remp remv remq
      fold-left fold-right
      find exists for-all memp memv memq
      assoc assv assq
      vector-map vector-for-each string-for-each))

  ;; Check if a symbol is a known-terminating collection HOF.
  (define (collection-hof? sym)
    (and (memq sym collection-hof-names) #t))

  ;; ---------------------------------------------------------------
  ;; Record accessor type resolution
  ;; ---------------------------------------------------------------

  ;; Resolve the return type of a record field accessor call.
  ;; Given an expression like (accessor-name var) and the type of var,
  ;; attempt to find the field type from the record type.
  ;; Returns the field type or #f if resolution fails.
  ;;
  ;; Accessor naming convention: record-name-field-name -> field-name
  ;; Also tries direct match of accessor-name as a field name.
  (define (resolve-accessor-type accessor-name var-type)
    (and (type-record? var-type)
         (let ((fields (type-record-fields var-type)))
           ;; Try direct field name match first
           (let ((direct (assq accessor-name fields)))
             (if direct
                 (cdr direct)
                 ;; Try to strip a prefix: look for the field with the
                 ;; longest suffix match to avoid ambiguity (e.g., -name vs -full-name)
                 (let ((acc-str (symbol->string accessor-name)))
                   (let loop ((remaining fields)
                              (best-type #f)
                              (best-len 0))
                     (if (null? remaining)
                         best-type
                         (let* ((field-name (caar remaining))
                                (field-str (symbol->string field-name))
                                (suffix (string-append "-" field-str))
                                (suffix-len (string-length suffix)))
                           (if (and (> (string-length acc-str) suffix-len)
                                    (string=? (substring acc-str
                                                (- (string-length acc-str) suffix-len)
                                                (string-length acc-str))
                                              suffix)
                                    (> suffix-len best-len))
                               (loop (cdr remaining) (cdar remaining) suffix-len)
                               (loop (cdr remaining) best-type best-len)))))))))))

  ;; ---------------------------------------------------------------
  ;; Phase 2: Definition extraction
  ;; ---------------------------------------------------------------

  ;; Extract function definitions from a list of expressions.
  ;; Handles both top-level and internal (nested) defines:
  ;;   (define (name params...) body...)
  ;;   (define name (lambda (params...) body...))
  ;;   (define name (case-lambda (formals body...) ...))
  ;;   letrec/letrec* bindings with lambda values
  ;; Recursively processes body expressions to find internal defines.
  ;; Returns alist of (name . body-exprs)
  (define (extract-definitions exprs)
    (let ((defs '()))
      (define (process-expr expr)
        (when (pair? expr)
          (cond
            ;; (define (name . params) body...)
            ((and (eq? (car expr) 'define)
                  (pair? (cdr expr))
                  (pair? (cadr expr))
                  (symbol? (caadr expr)))
             (let ((name (caadr expr))
                   (body (cddr expr)))
               (set! defs (cons (cons name body) defs))
               ;; Recurse into body to find internal defines
               (for-each process-expr body)))

            ;; (define name (lambda (...) body...))
            ((and (eq? (car expr) 'define)
                  (pair? (cdr expr))
                  (symbol? (cadr expr))
                  (pair? (cddr expr))
                  (pair? (caddr expr))
                  (eq? (car (caddr expr)) 'lambda)
                  (pair? (cdr (caddr expr))))
             (let ((name (cadr expr))
                   (body (cddr (caddr expr))))
               (set! defs (cons (cons name body) defs))
               ;; Recurse into body to find internal defines
               (for-each process-expr body)))

            ;; (define name (case-lambda clause...))
            ((and (eq? (car expr) 'define)
                  (pair? (cdr expr))
                  (symbol? (cadr expr))
                  (pair? (cddr expr))
                  (pair? (caddr expr))
                  (eq? (car (caddr expr)) 'case-lambda))
             (let* ((name (cadr expr))
                    (clauses (cdr (caddr expr)))
                    (all-bodies (apply append
                                      (map (lambda (c)
                                             (if (pair? c) (cdr c) '()))
                                           clauses))))
               (set! defs (cons (cons name all-bodies) defs))
               ;; Recurse into clause bodies to find internal defines
               (for-each process-expr all-bodies)))

            ;; (letrec ((name (lambda ...)) ...) body...)
            ;; (letrec* ((name (lambda ...)) ...) body...)
            ((and (memq (car expr) '(letrec letrec*))
                  (pair? (cdr expr))
                  (pair? (cadr expr)))
             (for-each
              (lambda (binding)
                (when (and (pair? binding)
                           (symbol? (car binding))
                           (pair? (cdr binding))
                           (pair? (cadr binding))
                           (eq? (car (cadr binding)) 'lambda)
                           (pair? (cdr (cadr binding))))
                  (let ((name (car binding))
                        (body (cddr (cadr binding))))
                    (set! defs (cons (cons name body) defs))
                    ;; Recurse into body to find internal defines
                    (for-each process-expr body))))
              (cadr expr))
             ;; Also recurse into the letrec body expressions
             (for-each process-expr (cddr expr)))

            ;; For other compound expressions, recurse to find nested defines
            (else
             (for-each
              (lambda (sub)
                (when (pair? sub)
                  (process-expr sub)))
              (cdr expr))))))

      (for-each process-expr exprs)
      (reverse defs)))

  ;; ---------------------------------------------------------------
  ;; Phase 2: Call site collection
  ;; ---------------------------------------------------------------

  ;; Collect all symbols in call position within body expressions
  ;; that match target-names. Skips quoted forms.
  ;; Distinguishes call position (car of application) from argument position:
  ;; only the car is checked as a potential call, then recursion proceeds
  ;; into the argument sub-expressions (cdr) only.
  ;; Calls to known-terminating collection HOFs (map, filter, fold-left, etc.)
  ;; are excluded because they represent bounded iteration, not user recursion.
  ;; Returns a deduplicated list of called function names.
  (define (collect-calls-in-body body-exprs target-names)
    (let ((calls '()))
      (define (walk expr)
        (when (pair? expr)
          (unless (eq? (car expr) 'quote)
            ;; If car is a target name and NOT a collection HOF, record the call
            (when (and (symbol? (car expr))
                       (memq (car expr) target-names)
                       (not (collection-hof? (car expr))))
              (set! calls (cons (car expr) calls)))
            ;; If car is a compound expression, recurse into it too
            (when (pair? (car expr))
              (walk (car expr)))
            ;; Recurse into argument sub-expressions only
            (for-each walk (cdr expr)))))
      (for-each walk body-exprs)
      (deduplicate calls)))

  ;; ---------------------------------------------------------------
  ;; Phase 2: Call graph construction
  ;; ---------------------------------------------------------------

  ;; Build a directed call graph from a list of expressions.
  ;; Returns an alist of (name . (list-of called-names)).
  ;; Each entry represents a function and the other defined functions it calls.
  (define (build-call-graph exprs)
    (let* ((defs (extract-definitions exprs))
           (defined-names (map car defs)))
      (map (lambda (def)
             (let ((name (car def))
                   (body (cdr def)))
               (cons name (collect-calls-in-body body defined-names))))
           defs)))

  ;; Look up edges for a node in the call graph.
  ;; Returns the list of called functions, or '() if not found.
  (define (call-graph-edges graph name)
    (let ((entry (assq name graph)))
      (if entry (cdr entry) '())))

  ;; ---------------------------------------------------------------
  ;; Phase 2: Tarjan's SCC algorithm
  ;; ---------------------------------------------------------------

  ;; Find all strongly connected components in a directed graph.
  ;; graph: alist of (node . (list-of successor-nodes))
  ;; Returns a list of SCCs, each SCC being a list of nodes.
  ;; SCCs with a single node that has no self-edge are trivial (non-recursive).
  (define (tarjan-scc graph)
    (let ((index-counter (vector 0))
          (stack '())
          (indices (make-eq-hashtable))
          (lowlinks (make-eq-hashtable))
          (on-stack (make-eq-hashtable))
          (result '()))

      (define (next-index!)
        (let ((i (vector-ref index-counter 0)))
          (vector-set! index-counter 0 (+ i 1))
          i))

      (define (strongconnect v)
        (let ((idx (next-index!)))
          (hashtable-set! indices v idx)
          (hashtable-set! lowlinks v idx)
          (set! stack (cons v stack))
          (hashtable-set! on-stack v #t)

          ;; Process successors
          (let ((successors (let ((entry (assq v graph)))
                              (if entry (cdr entry) '()))))
            (for-each
             (lambda (w)
               (cond
                 ((not (hashtable-contains? indices w))
                  ;; w not yet visited
                  (strongconnect w)
                  (hashtable-set! lowlinks v
                    (min (hashtable-ref lowlinks v 0)
                         (hashtable-ref lowlinks w 0))))
                 ((hashtable-ref on-stack w #f)
                  ;; w is on stack, part of current SCC
                  (hashtable-set! lowlinks v
                    (min (hashtable-ref lowlinks v 0)
                         (hashtable-ref indices w 0))))))
             successors))

          ;; If v is a root node, pop the SCC
          (when (= (hashtable-ref lowlinks v 0)
                   (hashtable-ref indices v 0))
            (let loop ((component '()))
              (let ((w (car stack)))
                (set! stack (cdr stack))
                (hashtable-set! on-stack w #f)
                (let ((new-component (cons w component)))
                  (if (eq? w v)
                      (set! result (cons new-component result))
                      (loop new-component))))))))

      ;; Process all nodes in the graph
      (for-each
       (lambda (entry)
         (unless (hashtable-contains? indices (car entry))
           (strongconnect (car entry))))
       graph)

      result))

  ;; ---------------------------------------------------------------
  ;; Phase 3: Do-form analysis
  ;; ---------------------------------------------------------------

  ;; Check if an expression references any of the given symbols.
  ;; Skips quoted forms.
  (define (expr-references-any? expr symbols)
    (cond
      ((null? symbols) #f)
      ((symbol? expr) (and (memq expr symbols) #t))
      ((not (pair? expr)) #f)
      ((eq? (car expr) 'quote) #f)
      (else (or (expr-references-any? (car expr) symbols)
                (expr-references-any? (cdr expr) symbols)))))

  ;; Analyze all do-forms in a list of expressions for termination issues.
  ;; Checks:
  ;;   - termination test is not trivially false (#f)
  ;;   - at least one loop variable has a step expression
  ;;   - termination test references at least one loop variable
  ;; Returns a list of termination-violation records with kind 'infinite-loop.
  (define (analyze-do-forms exprs)
    (let ((violations '()))
      (define (add-violation! do-expr reason)
        (set! violations
          (cons (make-termination-violation 'infinite-loop #f do-expr reason)
                violations)))

      (define (walk expr)
        (when (pair? expr)
          (unless (eq? (car expr) 'quote)
            (when (eq? (car expr) 'do)
              (check-do-form expr))
            ;; Walk car if it is a compound expression (for nested do-forms)
            (when (pair? (car expr))
              (walk (car expr)))
            ;; Walk sub-expressions
            (for-each (lambda (sub) (when (pair? sub) (walk sub)))
                      (cdr expr)))))

      (define (check-do-form do-expr)
        (when (and (pair? (cdr do-expr))
                   (pair? (cddr do-expr)))
          (let* ((bindings (cadr do-expr))
                 (termination (caddr do-expr))
                 ;; Extract loop variable names from bindings
                 (vars (if (and (pair? bindings) (list? bindings))
                           (let lp ((bs bindings) (acc '()))
                             (if (null? bs)
                                 (reverse acc)
                                 (lp (cdr bs)
                                     (if (and (pair? (car bs))
                                              (symbol? (caar bs)))
                                         (cons (caar bs) acc)
                                         acc))))
                           '()))
                 ;; Check if any binding has a step expression
                 (has-any-step?
                  (and (pair? bindings)
                       (let lp ((bs bindings))
                         (cond
                           ((null? bs) #f)
                           ((and (pair? (car bs))
                                 (pair? (cdar bs))
                                 (pair? (cddar bs)))
                            #t)
                           (else (lp (cdr bs))))))))
            (cond
              ;; Test is literally #f -- loop never exits
              ((and (pair? termination)
                    (eq? (car termination) #f))
               (add-violation! do-expr
                 "do-form has unreachable exit condition"))

              ;; No step expressions -- loop variables never change
              ((and (not (null? vars)) (not has-any-step?))
               (add-violation! do-expr
                 "do-form has no step expressions; loop variables never change"))

              ;; Test does not reference any loop variable
              ((and (pair? termination)
                    (not (null? vars))
                    has-any-step?
                    (not (expr-references-any? (car termination) vars)))
               (add-violation! do-expr
                 "do-form exit test does not reference any loop variable"))))))

      (for-each walk exprs)
      (reverse violations)))

  ;; ---------------------------------------------------------------
  ;; Phase 4: Named-let analysis
  ;; ---------------------------------------------------------------

  ;; Check if an expression is a decreasing pattern for the given variable.
  ;; Numeric: (- x 1), (sub1 x), (fx- x 1)
  ;; Structural: (cdr x), (cddr x), (list-tail x ...)
  ;; Type-aware: when var-type is provided, also recognizes record accessor
  ;; calls that return a nullable self-referential type (linked-list traversal).
  ;; var-type is optional (defaults to #f when not available).
  (define decreasing-expr?
    (case-lambda
      ((expr var) (decreasing-expr? expr var #f))
      ((expr var var-type)
       (and (pair? expr)
            (or
              ;; (- var 1) or (- var <positive>)
              (and (eq? (car expr) '-)
                   (pair? (cdr expr))
                   (eq? (cadr expr) var)
                   (pair? (cddr expr))
                   (number? (caddr expr))
                   (> (caddr expr) 0))
              ;; (sub1 var)
              (and (eq? (car expr) 'sub1)
                   (pair? (cdr expr))
                   (eq? (cadr expr) var))
              ;; (fx- var 1) or (fx- var <positive>)
              (and (eq? (car expr) 'fx-)
                   (pair? (cdr expr))
                   (eq? (cadr expr) var)
                   (pair? (cddr expr))
                   (number? (caddr expr))
                   (> (caddr expr) 0))
              ;; (cdr var)
              (and (eq? (car expr) 'cdr)
                   (pair? (cdr expr))
                   (eq? (cadr expr) var))
              ;; (cddr var)
              (and (eq? (car expr) 'cddr)
                   (pair? (cdr expr))
                   (eq? (cadr expr) var))
              ;; (list-tail var ...)
              (and (eq? (car expr) 'list-tail)
                   (pair? (cdr expr))
                   (eq? (cadr expr) var))
              ;; Type-aware: (accessor var) where accessor returns a type
              ;; containing Null (nullable self-reference in a record = linked-list pattern)
              (and var-type
                   (type-record? var-type)
                   (symbol? (car expr))
                   (pair? (cdr expr))
                   (eq? (cadr expr) var)
                   (null? (cddr expr))  ;; single-argument call
                   (let ((field-type (resolve-accessor-type (car expr) var-type)))
                     (and field-type
                          (type-contains-null? field-type)))))))))

  ;; Check if an expression monotonically changes the given variable
  ;; (either increasing or decreasing). This is sufficient for termination
  ;; when paired with a guard that references the variable.
  ;; Includes all decreasing patterns plus:
  ;; Increasing: (+ x 1), (add1 x), (fx+ x 1)
  ;; var-type is optional (defaults to #f).
  (define monotonic-expr?
    (case-lambda
      ((expr var) (monotonic-expr? expr var #f))
      ((expr var var-type)
       (or (decreasing-expr? expr var var-type)
           (and (pair? expr)
                (or
                  ;; (+ var <positive>) or (+ <positive> var)
                  (and (eq? (car expr) '+)
                       (pair? (cdr expr))
                       (pair? (cddr expr))
                       (or (and (eq? (cadr expr) var)
                                (number? (caddr expr))
                                (> (caddr expr) 0))
                           (and (number? (cadr expr))
                                (> (cadr expr) 0)
                                (eq? (caddr expr) var))))
                  ;; (add1 var)
                  (and (eq? (car expr) 'add1)
                       (pair? (cdr expr))
                       (eq? (cadr expr) var))
                  ;; (fx+ var <positive>)
                  (and (eq? (car expr) 'fx+)
                       (pair? (cdr expr))
                       (eq? (cadr expr) var)
                       (pair? (cddr expr))
                       (number? (caddr expr))
                       (> (caddr expr) 0))))))))

  ;; Check if an expression contains a recursive call to loop-name.
  ;; Skips quoted forms.
  (define (contains-call? expr loop-name)
    (cond
      ((symbol? expr) #f)
      ((not (pair? expr)) #f)
      ((eq? (car expr) 'quote) #f)
      ((and (eq? (car expr) loop-name)) #t)
      (else (or (contains-call? (car expr) loop-name)
                (contains-call? (cdr expr) loop-name)))))

  ;; Check if ALL recursive calls to loop-name use a monotonically changing
  ;; argument for at least one of the given variables.
  ;; Conservative: returns #f if ANY call site lacks a monotonic argument,
  ;; ensuring non-terminating code with mixed call patterns is detected.
  ;; A call is (loop-name arg1 arg2 ...) and we check each arg against
  ;; the corresponding variable for a monotonic change pattern.
  ;; type-env is optional (defaults to '()).
  (define has-decreasing-call?
    (case-lambda
      ((body-exprs loop-name vars)
       (has-decreasing-call? body-exprs loop-name vars '()))
      ((body-exprs loop-name vars type-env)
       (let ((found-any #f)    ;; have we seen at least one recursive call?
             (all-decrease #t)) ;; do ALL calls so far have a monotonic arg?
         (define (walk expr)
           (when (and all-decrease (pair? expr))
             (unless (eq? (car expr) 'quote)
               (when (eq? (car expr) loop-name)
                 ;; This is a recursive call -- check arguments
                 (set! found-any #t)
                 (let ((this-decreases #f))
                   (let check-args ((args (cdr expr)) (params vars))
                     (when (and (pair? args) (pair? params))
                       (when (monotonic-expr? (car args) (car params)
                               (type-env-lookup type-env (car params)))
                         (set! this-decreases #t))
                       (check-args (cdr args) (cdr params))))
                   (unless this-decreases
                     (set! all-decrease #f))))
               ;; Recurse
               (when (pair? (car expr))
                 (walk (car expr)))
               (for-each (lambda (sub) (when (pair? sub) (walk sub)))
                         (cdr expr)))))
         (for-each walk body-exprs)
         (and found-any all-decrease)))))

  ;; Check if an expression is a base-case test for the given variables.
  ;; Numeric: (= x 0), (zero? x), (< x 1), (<= x 0)
  ;; Structural: (null? x), (not (pair? x))
  ;; Type-aware: when type-env is provided and a variable has type (List T)
  ;; or a union type containing Null, (null? var) is confirmed as a valid base case.
  ;; type-env is optional (defaults to '()).
  (define base-case-test?
    (case-lambda
      ((expr vars) (base-case-test? expr vars '()))
      ((expr vars type-env)
       (and (pair? expr)
            (or
              ;; (= var <expr>) or (= <expr> var) where var is a loop variable
              ;; and the other operand is not itself a loop variable (i.e., it's a fixed bound)
              (and (eq? (car expr) '=)
                   (pair? (cdr expr))
                   (pair? (cddr expr))
                   (or (and (memq (cadr expr) vars)
                            (not (memq (caddr expr) vars)))
                       (and (not (memq (cadr expr) vars))
                            (memq (caddr expr) vars))))
              ;; (zero? var)
              (and (eq? (car expr) 'zero?)
                   (pair? (cdr expr))
                   (and (memq (cadr expr) vars) #t))
              ;; (< var N) where N is a number or a non-loop-variable
              (and (eq? (car expr) '<)
                   (pair? (cdr expr))
                   (pair? (cddr expr))
                   (memq (cadr expr) vars)
                   (not (memq (caddr expr) vars)))
              ;; (> N var) or (> <expr> var) where var is a loop variable
              (and (eq? (car expr) '>)
                   (pair? (cdr expr))
                   (pair? (cddr expr))
                   (memq (caddr expr) vars)
                   (not (memq (cadr expr) vars)))
              ;; (<= var N) where N is not a loop variable
              (and (eq? (car expr) '<=)
                   (pair? (cdr expr))
                   (pair? (cddr expr))
                   (memq (cadr expr) vars)
                   (not (memq (caddr expr) vars)))
              ;; (>= N var) where var is a loop variable
              (and (eq? (car expr) '>=)
                   (pair? (cdr expr))
                   (pair? (cddr expr))
                   (memq (caddr expr) vars)
                   (not (memq (cadr expr) vars)))
              ;; (null? var)
              (and (eq? (car expr) 'null?)
                   (pair? (cdr expr))
                   (and (memq (cadr expr) vars) #t))
              ;; (not (pair? var))
              (and (eq? (car expr) 'not)
                   (pair? (cdr expr))
                   (pair? (cadr expr))
                   (eq? (caadr expr) 'pair?)
                   (pair? (cdadr expr))
                   (memq (cadadr expr) vars)
                   #t))))))

  ;; Check if the body has a base case -- a conditional branch that does
  ;; not contain a recursive call to loop-name.
  ;; Looks for if/cond/when/unless guards.
  ;; type-env is optional (defaults to '()).
  (define has-base-case?
    (case-lambda
      ((body-exprs loop-name vars)
       (has-base-case? body-exprs loop-name vars '()))
      ((body-exprs loop-name vars type-env)
       (let ((found #f))
         (define (walk expr)
           (when (and (not found) (pair? expr))
             (unless (eq? (car expr) 'quote)
               (cond
                 ;; (if test consequent alternative)
                 ;; Base case if test is a base-case-test and consequent doesn't recurse,
                 ;; OR if alternative doesn't recurse.
                 ((eq? (car expr) 'if)
                  (when (and (pair? (cdr expr)) (pair? (cddr expr)))
                    (let ((test (cadr expr))
                          (consequent (caddr expr))
                          (alternative (if (pair? (cdddr expr)) (cadddr expr) #f)))
                      ;; Check if test is a base-case test and consequent doesn't recurse
                      (when (and (base-case-test? test vars type-env)
                                 (not (contains-call? consequent loop-name)))
                        (set! found #t))
                      ;; Recurse into branches to find nested guards
                      (walk consequent)
                      (when alternative (walk alternative)))))

                 ;; (cond (test expr ...) ...) -- base case if any clause
                 ;; has a test that's a base-case-test and body doesn't recurse
                 ((eq? (car expr) 'cond)
                  (for-each
                    (lambda (clause)
                      (when (and (pair? clause) (pair? (cdr clause)))
                        (let ((test (car clause))
                              (body (cdr clause)))
                          (when (and (or (base-case-test? test vars type-env)
                                         (eq? test 'else))
                                     (not (contains-call? body loop-name)))
                            (set! found #t))
                          ;; Recurse into clause bodies
                          (for-each walk body))))
                    (cdr expr)))

                 ;; (when test body...) -- implicit base case: if test is false,
                 ;; loop returns void (doesn't recurse)
                 ;; Conservative: only count if test references a loop variable,
                 ;; otherwise the implicit void path may be unreachable.
                 ((eq? (car expr) 'when)
                  (when (pair? (cdr expr))
                    (let ((test (cadr expr))
                          (body (cddr expr)))
                      (when (and (contains-call? body loop-name)
                                 (not (contains-call? test loop-name))
                                 (expr-references-any? test vars))
                        (set! found #t))
                      (for-each walk body))))

                 ;; (unless test body...) -- implicit base case: if test is true,
                 ;; loop returns void (doesn't recurse)
                 ;; Conservative: only count if test references a loop variable.
                 ((eq? (car expr) 'unless)
                  (when (pair? (cdr expr))
                    (let ((test (cadr expr))
                          (body (cddr expr)))
                      (when (and (contains-call? body loop-name)
                                 (not (contains-call? test loop-name))
                                 (expr-references-any? test vars))
                        (set! found #t))
                      (for-each walk body))))

                 ;; Generic: recurse into sub-expressions
                 (else
                  (when (pair? (car expr))
                    (walk (car expr)))
                  (for-each (lambda (sub) (when (pair? sub) (walk sub)))
                            (cdr expr)))))))
         (for-each walk body-exprs)
         found))))

  ;; Analyze all named-let forms in a list of expressions for termination issues.
  ;; A named-let looks like: (let name ((var init) ...) body ...)
  ;; where name is a symbol.
  ;; Checks:
  ;;   - recursive calls use decreasing arguments
  ;;   - a base case exists (conditional branch that doesn't recurse)
  ;; type-env is optional (defaults to '()).
  ;; Returns a list of termination-violation records.
  (define analyze-named-let-forms
    (case-lambda
      ((exprs) (analyze-named-let-forms exprs '()))
      ((exprs type-env)
       (let ((violations '()))
         (define (add-violation! kind loop-name expr reason)
           (set! violations
             (cons (make-termination-violation kind loop-name expr reason)
                   violations)))

         (define (walk expr)
           (when (pair? expr)
             (unless (eq? (car expr) 'quote)
               ;; Check for named-let: (let <symbol> ((var init) ...) body ...)
               (when (and (eq? (car expr) 'let)
                          (pair? (cdr expr))
                          (symbol? (cadr expr))
                          (pair? (cddr expr))
                          (pair? (cdddr expr)))
                 (check-named-let expr))
               ;; Walk car if compound
               (when (pair? (car expr))
                 (walk (car expr)))
               ;; Walk sub-expressions
               (for-each (lambda (sub) (when (pair? sub) (walk sub)))
                         (cdr expr)))))

         (define (check-named-let expr)
           (let* ((loop-name (cadr expr))
                  (bindings (caddr expr))
                  (body (cdddr expr))
                  ;; Extract variable names from bindings
                  (vars (if (and (pair? bindings) (list? bindings))
                            (let lp ((bs bindings) (acc '()))
                              (if (null? bs)
                                  (reverse acc)
                                  (lp (cdr bs)
                                      (if (and (pair? (car bs))
                                               (symbol? (caar bs)))
                                          (cons (caar bs) acc)
                                          acc))))
                            '()))
                  ;; Check if body contains recursive calls
                  (has-recursion? (contains-call? body loop-name)))

             ;; Only analyze if the named-let actually recurses
             (when has-recursion?
               (cond
                 ;; No variables or no decreasing argument in recursive calls
                 ((or (null? vars)
                      (not (has-decreasing-call? body loop-name vars type-env)))
                  (add-violation! 'no-decreasing-arg loop-name expr
                    (string-append "named-let \"" (symbol->string loop-name)
                      "\" has no decreasing argument in recursive call(s)")))

                 ;; Has decreasing args but no base case
                 ((not (has-base-case? body loop-name vars type-env))
                  (add-violation! 'no-base-case loop-name expr
                    (string-append "named-let \"" (symbol->string loop-name)
                      "\" has no reachable base case")))))))

         (for-each walk exprs)
         (reverse violations)))))

  ;; Like has-decreasing-call? but only accepts strictly decreasing patterns
  ;; (not monotonic/increasing). Used for direct recursion where increasing
  ;; toward a base case is not a valid termination pattern.
  ;; type-env is optional (defaults to '()).
  (define has-strictly-decreasing-call?
    (case-lambda
      ((body-exprs func-name vars)
       (has-strictly-decreasing-call? body-exprs func-name vars '()))
      ((body-exprs func-name vars type-env)
       (let ((found-any #f)
             (all-decrease #t))
         (define (walk expr)
           (when (and all-decrease (pair? expr))
             (unless (eq? (car expr) 'quote)
               (when (eq? (car expr) func-name)
                 (set! found-any #t)
                 (let ((this-decreases #f))
                   (let check-args ((args (cdr expr)) (params vars))
                     (when (and (pair? args) (pair? params))
                       (when (decreasing-expr? (car args) (car params)
                               (type-env-lookup type-env (car params)))
                         (set! this-decreases #t))
                       (check-args (cdr args) (cdr params))))
                   (unless this-decreases
                     (set! all-decrease #f))))
               (when (pair? (car expr))
                 (walk (car expr)))
               (for-each (lambda (sub) (when (pair? sub) (walk sub)))
                         (cdr expr)))))
         (for-each walk body-exprs)
         (and found-any all-decrease)))))

  ;; ---------------------------------------------------------------
  ;; Phase 5: Direct recursion analysis
  ;; ---------------------------------------------------------------

  ;; Extract formal parameter list from a definition form.
  ;; Handles:
  ;;   (define (name params...) body...)        -> (params...)
  ;;   (define name (lambda (params...) body...)) -> (params...)
  ;;   letrec/letrec* binding: (name (lambda (params...) body...)) -> (params...)
  ;; Returns the parameter list or #f if it can't be extracted.
  (define (extract-formals expr)
    (cond
      ;; (define (name . formals) body...) -- formals is cdr of (name . formals)
      ((and (pair? expr)
            (eq? (car expr) 'define)
            (pair? (cdr expr))
            (pair? (cadr expr))
            (symbol? (caadr expr)))
       (let ((formals (cdadr expr)))
         (if (list? formals) formals #f)))

      ;; (define name (lambda (formals...) body...))
      ((and (pair? expr)
            (eq? (car expr) 'define)
            (pair? (cdr expr))
            (symbol? (cadr expr))
            (pair? (cddr expr))
            (pair? (caddr expr))
            (eq? (car (caddr expr)) 'lambda)
            (pair? (cdr (caddr expr)))
            (list? (cadr (caddr expr))))
       (cadr (caddr expr)))

      ;; letrec binding: (name (lambda (formals...) body...))
      ((and (pair? expr)
            (symbol? (car expr))
            (pair? (cdr expr))
            (pair? (cadr expr))
            (eq? (car (cadr expr)) 'lambda)
            (pair? (cdr (cadr expr)))
            (list? (cadr (cadr expr))))
       (cadr (cadr expr)))

      (else #f)))

  ;; Find the original definition form for a function name in the expression list.
  ;; Used to attach the source form to violations.
  (define (find-definition-form exprs name)
    (let ((result #f))
      (define (search expr)
        (when (and (not result) (pair? expr))
          (cond
            ;; (define (name ...) ...)
            ((and (eq? (car expr) 'define)
                  (pair? (cdr expr))
                  (pair? (cadr expr))
                  (eq? (caadr expr) name))
             (set! result expr))
            ;; (define name (lambda ...))
            ((and (eq? (car expr) 'define)
                  (pair? (cdr expr))
                  (eq? (cadr expr) name))
             (set! result expr))
            ;; letrec/letrec* bindings
            ((and (memq (car expr) '(letrec letrec*))
                  (pair? (cdr expr))
                  (pair? (cadr expr)))
             (for-each
               (lambda (binding)
                 (when (and (not result)
                            (pair? binding)
                            (eq? (car binding) name))
                   (set! result expr)))
               (cadr expr))
             ;; Recurse into letrec body
             (for-each search (cddr expr)))
            (else
             (for-each (lambda (sub) (when (pair? sub) (search sub)))
                       (cdr expr))))))
      (for-each search exprs)
      result))

  ;; Extract formals for a named function from the expression list.
  ;; Walks expressions to find the definition and extract its formals.
  (define (find-formals-for exprs name)
    (let ((result #f))
      (define (search expr)
        (when (and (not result) (pair? expr))
          (cond
            ;; (define (name params...) body...)
            ((and (eq? (car expr) 'define)
                  (pair? (cdr expr))
                  (pair? (cadr expr))
                  (eq? (caadr expr) name))
             (set! result (extract-formals expr)))
            ;; (define name (lambda (params...) body...))
            ((and (eq? (car expr) 'define)
                  (pair? (cdr expr))
                  (eq? (cadr expr) name)
                  (pair? (cddr expr)))
             (set! result (extract-formals expr)))
            ;; letrec/letrec* bindings
            ((and (memq (car expr) '(letrec letrec*))
                  (pair? (cdr expr))
                  (pair? (cadr expr)))
             (for-each
               (lambda (binding)
                 (when (and (not result)
                            (pair? binding)
                            (eq? (car binding) name))
                   (set! result (extract-formals binding))))
               (cadr expr))
             ;; Recurse into letrec body
             (for-each search (cddr expr)))
            (else
             (for-each (lambda (sub) (when (pair? sub) (search sub)))
                       (cdr expr))))))
      (for-each search exprs)
      result))

  ;; Analyze directly recursive functions for termination.
  ;; Uses call graph + SCC to identify direct recursion (single-node SCCs
  ;; with a self-edge), then reuses has-decreasing-call? and has-base-case?
  ;; from named-let analysis.
  ;; type-env is optional (defaults to '()).
  (define analyze-direct-recursion
    (case-lambda
      ((exprs) (analyze-direct-recursion exprs '()))
      ((exprs type-env)
       (let* ((graph (build-call-graph exprs))
              (sccs (tarjan-scc graph))
              (violations '()))

         (define (add-violation! kind func-name expr reason)
           (set! violations
             (cons (make-termination-violation kind func-name expr reason)
                   violations)))

         ;; Process each SCC
         (for-each
           (lambda (scc)
             ;; Only handle direct recursion: single-node SCC with self-edge
             (when (and (= (length scc) 1)
                        (memq (car scc) (call-graph-edges graph (car scc))))
               (let* ((name (car scc))
                      (formals (find-formals-for exprs name))
                      (def-entry (assq name graph))
                      (body-entry (assq name (extract-definitions exprs)))
                      (body (if body-entry (cdr body-entry) '()))
                      (def-form (find-definition-form exprs name)))
                 ;; Only analyze if we could extract formals
                 (when formals
                   (cond
                     ;; No formals or no strictly decreasing argument in any recursive call
                     ((or (null? formals)
                          (not (has-strictly-decreasing-call? body name formals type-env)))
                      (add-violation! 'no-decreasing-arg name
                        (or def-form (list 'define name '...))
                        (string-append "recursive function \""
                          (symbol->string name)
                          "\" has no decreasing argument in recursive call(s)")))

                     ;; Has decreasing args but no base case
                     ((not (has-base-case? body name formals type-env))
                      (add-violation! 'no-base-case name
                        (or def-form (list 'define name '...))
                        (string-append "recursive function \""
                          (symbol->string name)
                          "\" has no reachable base case"))))))))
           sccs)

         (reverse violations)))))

  ;; ---------------------------------------------------------------
  ;; Phase 6: Mutual recursion analysis
  ;; ---------------------------------------------------------------

  ;; Collect intra-SCC call expressions from body expressions.
  ;; Returns a list of (callee-name arg-exprs...) for calls to SCC members.
  ;; Includes self-calls (since self-edges within a multi-node SCC must also
  ;; be verified as decreasing).
  (define (collect-intra-scc-calls body-exprs scc-members)
    (let ((calls '()))
      (define (walk expr)
        (when (pair? expr)
          (unless (eq? (car expr) 'quote)
            ;; If car is an SCC member name, record the full call
            (when (and (symbol? (car expr))
                       (memq (car expr) scc-members))
              (set! calls (cons expr calls)))
            ;; Walk car if compound
            (when (pair? (car expr))
              (walk (car expr)))
            ;; Walk argument sub-expressions
            (for-each (lambda (sub) (when (pair? sub) (walk sub)))
                      (cdr expr)))))
      (for-each walk body-exprs)
      calls))

  ;; Check if a call expression has at least one strictly decreasing argument
  ;; relative to the caller's formals. Checks each argument positionally and
  ;; also checks if any argument is a decreasing expression of ANY formal.
  ;; type-env is optional (defaults to '()).
  (define call-has-decreasing-arg?
    (case-lambda
      ((call-expr caller-formals)
       (call-has-decreasing-arg? call-expr caller-formals '()))
      ((call-expr caller-formals type-env)
       (let ((args (cdr call-expr)))
         (let check-args ((remaining-args args))
           (if (null? remaining-args)
               #f
               (let check-formals ((formals caller-formals))
                 (cond
                   ((null? formals)
                    (check-args (cdr remaining-args)))
                   ((decreasing-expr? (car remaining-args) (car formals)
                      (type-env-lookup type-env (car formals)))
                    #t)
                   (else
                    (check-formals (cdr formals)))))))))))

  ;; Check if a test expression references any formal parameter of the SCC functions.
  ;; Used to ensure when/unless guards depend on changing state (not constant tests).
  (define (scc-test-references-param? test exprs scc-members)
    (let ((all-formals
           (let collect ((members scc-members) (acc '()))
             (if (null? members)
                 acc
                 (let ((formals (find-formals-for exprs (car members))))
                   (collect (cdr members)
                            (if formals (append formals acc) acc)))))))
      (expr-references-any? test all-formals)))

  ;; Check if at least one function in the SCC has a base case --
  ;; a conditional branch that does not call ANY SCC member.
  (define (scc-has-base-case? exprs scc-members)
    (let ((found #f))
      (define (contains-scc-call? expr)
        (cond
          ((symbol? expr) #f)
          ((not (pair? expr)) #f)
          ((eq? (car expr) 'quote) #f)
          ((and (symbol? (car expr))
                (memq (car expr) scc-members)) #t)
          (else (or (contains-scc-call? (car expr))
                    (contains-scc-call? (cdr expr))))))

      (define (check-body body-exprs)
        (define (walk expr)
          (when (and (not found) (pair? expr))
            (unless (eq? (car expr) 'quote)
              (cond
                ;; (if test consequent alternative)
                ((eq? (car expr) 'if)
                 (when (and (pair? (cdr expr)) (pair? (cddr expr)))
                   (let ((test (cadr expr))
                         (consequent (caddr expr))
                         (alternative (if (pair? (cdddr expr)) (cadddr expr) #f)))
                     (when (and (not (contains-scc-call? test))
                                (or (not (contains-scc-call? consequent))
                                    (and alternative
                                         (not (contains-scc-call? alternative)))))
                       (set! found #t))
                     (walk consequent)
                     (when alternative (walk alternative)))))

                ;; (cond (test body...) ...)
                ((eq? (car expr) 'cond)
                 (for-each
                   (lambda (clause)
                     (when (and (pair? clause) (pair? (cdr clause)))
                       (let ((body (cdr clause)))
                         (when (not (contains-scc-call? body))
                           (set! found #t))
                         (for-each walk body))))
                   (cdr expr)))

                ;; (when test body...) -- if body contains a recursive call,
                ;; the implicit else (when test is false) is a no-op base case.
                ;; Conservative: test must reference a function parameter to ensure
                ;; the implicit base-case path is reachable (not a constant like #t).
                ((eq? (car expr) 'when)
                 (when (pair? (cdr expr))
                   (let ((test (cadr expr))
                         (body (cddr expr)))
                     (when (and (contains-scc-call? body)
                                (not (contains-scc-call? test))
                                (scc-test-references-param? test exprs scc-members))
                       (set! found #t))
                     (for-each walk body))))

                ;; (unless test body...) -- if body contains a recursive call,
                ;; the implicit else (when test is true) is a no-op base case.
                ;; Conservative: test must reference a function parameter.
                ((eq? (car expr) 'unless)
                 (when (pair? (cdr expr))
                   (let ((test (cadr expr))
                         (body (cddr expr)))
                     (when (and (contains-scc-call? body)
                                (not (contains-scc-call? test))
                                (scc-test-references-param? test exprs scc-members))
                       (set! found #t))
                     (for-each walk body))))

                (else
                 (when (pair? (car expr))
                   (walk (car expr)))
                 (for-each (lambda (sub) (when (pair? sub) (walk sub)))
                           (cdr expr)))))))
        (for-each walk body-exprs))

      ;; Check each function in the SCC for a base case
      (let ((defs (extract-definitions exprs)))
        (for-each
          (lambda (member)
            (unless found
              (let ((entry (assq member defs)))
                (when entry
                  (check-body (cdr entry))))))
          scc-members))
      found))

  ;; Analyze mutually recursive function groups for termination.
  ;; For each multi-node SCC in the call graph:
  ;;   - Check that every intra-SCC call edge passes a strictly decreasing argument
  ;;   - Check that at least one function in the SCC has a base case
  ;; If any call edge cannot be proven decreasing, flag all functions in the SCC.
  ;; type-env is optional (defaults to '()).
  (define analyze-mutual-recursion
    (case-lambda
      ((exprs) (analyze-mutual-recursion exprs '()))
      ((exprs type-env)
       (let* ((graph (build-call-graph exprs))
              (sccs (tarjan-scc graph))
              (defs (extract-definitions exprs))
              (violations '()))

         (define (add-violation! kind func-name expr reason)
           (set! violations
             (cons (make-termination-violation kind func-name expr reason)
                   violations)))

         ;; Process each multi-node SCC
         (for-each
           (lambda (scc)
             (when (> (length scc) 1)
               (let* ((scc-names scc)
                      ;; Check if all intra-SCC call edges have a decreasing argument
                      (all-edges-decrease
                       (let check-members ((members scc-names))
                         (if (null? members)
                             #t
                             (let* ((name (car members))
                                    (formals (find-formals-for exprs name))
                                    (body-entry (assq name defs))
                                    (body (if body-entry (cdr body-entry) '()))
                                    (intra-calls (collect-intra-scc-calls body scc-names)))
                               (if (or (not formals)
                                       (null? formals))
                                   ;; Can't extract formals -- conservative: fail
                                   #f
                                   (let check-calls ((calls intra-calls))
                                     (cond
                                       ((null? calls)
                                        (check-members (cdr members)))
                                       ((call-has-decreasing-arg? (car calls) formals type-env)
                                        (check-calls (cdr calls)))
                                       (else #f)))))))))

                 (cond
                   ;; Not all edges decrease -- flag all functions
                   ((not all-edges-decrease)
                    (let ((group-str (string-append "("
                                       (apply string-append
                                         (let build ((names (sort-symbols* scc-names)) (acc '()))
                                           (if (null? names)
                                               (reverse acc)
                                               (build (cdr names)
                                                      (cons (if (null? acc)
                                                                (symbol->string (car names))
                                                                (string-append ", " (symbol->string (car names))))
                                                            acc)))))
                                       ")")))
                      (for-each
                        (lambda (name)
                          (add-violation! 'no-decreasing-arg name
                            (or (find-definition-form exprs name)
                                (list 'define name '...))
                            (string-append "mutual recursion group " group-str
                              " has no decreasing argument across call edges")))
                        scc-names)))

                   ;; All edges decrease but no base case in the group
                   ((not (scc-has-base-case? exprs scc-names))
                    (let ((group-str (string-append "("
                                       (apply string-append
                                         (let build ((names (sort-symbols* scc-names)) (acc '()))
                                           (if (null? names)
                                               (reverse acc)
                                               (build (cdr names)
                                                      (cons (if (null? acc)
                                                                (symbol->string (car names))
                                                                (string-append ", " (symbol->string (car names))))
                                                            acc)))))
                                       ")")))
                      (for-each
                        (lambda (name)
                          (add-violation! 'no-base-case name
                            (or (find-definition-form exprs name)
                                (list 'define name '...))
                            (string-append "mutual recursion group " group-str
                              " has no reachable base case")))
                        scc-names)))))))
           sccs)

         (reverse violations)))))

  ;; Helper: sort symbols for deterministic output in violation messages
  (define (sort-symbols* syms)
    (list-sort (lambda (a b)
                 (string<? (symbol->string a) (symbol->string b)))
               syms))

  ;; ---------------------------------------------------------------
  ;; Main entry point
  ;; ---------------------------------------------------------------

  ;; check-termination : (list-of expr) x type-env [x max-definitions] -> (list-of termination-violation)
  ;; Analyzes expressions for potential non-termination.
  ;; Optional max-definitions parameter: when set, skip call-graph-based analysis
  ;; (direct recursion, mutual recursion) if the program has more definitions than this limit.
  ;; A value of 0 disables call-graph analysis entirely. #f means no limit (default).
  (define check-termination
    (case-lambda
      ((exprs type-env)
       (check-termination exprs type-env #f))
      ((exprs type-env max-definitions)
       (let ((do-violations (analyze-do-forms exprs))
             (named-let-violations (analyze-named-let-forms exprs type-env)))
         (if (and max-definitions
                  (let ((defs (extract-definitions exprs)))
                    (> (length defs) max-definitions)))
             ;; Skip call-graph analysis when over the depth limit
             (append do-violations named-let-violations)
             ;; Full analysis
             (append do-violations
                     named-let-violations
                     (analyze-direct-recursion exprs type-env)
                     (analyze-mutual-recursion exprs type-env)))))))
)
