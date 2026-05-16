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
          analyze-named-let-forms)
  (import (rnrs))

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
  ;; Returns a deduplicated list of called function names.
  (define (collect-calls-in-body body-exprs target-names)
    (let ((calls '()))
      (define (walk expr)
        (when (pair? expr)
          (unless (eq? (car expr) 'quote)
            ;; If car is a target name, record the call
            (when (and (symbol? (car expr))
                       (memq (car expr) target-names))
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
                 "do-form test is always false (#f)"))

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
                 "do-form test does not reference any loop variable"))))))

      (for-each walk exprs)
      (reverse violations)))

  ;; ---------------------------------------------------------------
  ;; Phase 4: Named-let analysis
  ;; ---------------------------------------------------------------

  ;; Check if an expression is a decreasing pattern for the given variable.
  ;; Numeric: (- x 1), (sub1 x), (fx- x 1)
  ;; Structural: (cdr x), (cddr x), (list-tail x ...)
  (define (decreasing-expr? expr var)
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
                (eq? (cadr expr) var)))))

  ;; Check if an expression monotonically changes the given variable
  ;; (either increasing or decreasing). This is sufficient for termination
  ;; when paired with a guard that references the variable.
  ;; Includes all decreasing patterns plus:
  ;; Increasing: (+ x 1), (add1 x), (fx+ x 1)
  (define (monotonic-expr? expr var)
    (or (decreasing-expr? expr var)
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
                    (> (caddr expr) 0))))))

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
  (define (has-decreasing-call? body-exprs loop-name vars)
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
                    (when (monotonic-expr? (car args) (car params))
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
      (and found-any all-decrease)))

  ;; Check if an expression is a base-case test for the given variables.
  ;; Numeric: (= x 0), (zero? x), (< x 1), (<= x 0)
  ;; Structural: (null? x), (not (pair? x))
  (define (base-case-test? expr vars)
    (and (pair? expr)
         (or
           ;; (= var 0) or (= 0 var)
           (and (eq? (car expr) '=)
                (pair? (cdr expr))
                (pair? (cddr expr))
                (or (and (memq (cadr expr) vars) (eqv? (caddr expr) 0))
                    (and (eqv? (cadr expr) 0) (memq (caddr expr) vars))))
           ;; (zero? var)
           (and (eq? (car expr) 'zero?)
                (pair? (cdr expr))
                (memq (cadr expr) vars)
                #t)
           ;; (< var 1)
           (and (eq? (car expr) '<)
                (pair? (cdr expr))
                (pair? (cddr expr))
                (memq (cadr expr) vars)
                (number? (caddr expr))
                (<= (caddr expr) 1)
                #t)
           ;; (<= var 0)
           (and (eq? (car expr) '<=)
                (pair? (cdr expr))
                (pair? (cddr expr))
                (memq (cadr expr) vars)
                (number? (caddr expr))
                (<= (caddr expr) 0)
                #t)
           ;; (null? var)
           (and (eq? (car expr) 'null?)
                (pair? (cdr expr))
                (memq (cadr expr) vars)
                #t)
           ;; (not (pair? var))
           (and (eq? (car expr) 'not)
                (pair? (cdr expr))
                (pair? (cadr expr))
                (eq? (caadr expr) 'pair?)
                (pair? (cdadr expr))
                (memq (cadadr expr) vars)
                #t))))

  ;; Check if the body has a base case -- a conditional branch that does
  ;; not contain a recursive call to loop-name.
  ;; Looks for if/cond/when/unless guards.
  (define (has-base-case? body-exprs loop-name vars)
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
                   (when (and (base-case-test? test vars)
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
                       (when (and (or (base-case-test? test vars)
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
      found))

  ;; Analyze all named-let forms in a list of expressions for termination issues.
  ;; A named-let looks like: (let name ((var init) ...) body ...)
  ;; where name is a symbol.
  ;; Checks:
  ;;   - recursive calls use decreasing arguments
  ;;   - a base case exists (conditional branch that doesn't recurse)
  ;; Returns a list of termination-violation records.
  (define (analyze-named-let-forms exprs)
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
                   (not (has-decreasing-call? body loop-name vars)))
               (add-violation! 'no-decreasing-arg loop-name expr
                 (string-append "named-let '" (symbol->string loop-name)
                   "' has no decreasing argument in recursive call(s)")))

              ;; Has decreasing args but no base case
              ((not (has-base-case? body loop-name vars))
               (add-violation! 'no-base-case loop-name expr
                 (string-append "named-let '" (symbol->string loop-name)
                   "' decreases but has no base case to stop recursion")))))))

      (for-each walk exprs)
      (reverse violations)))

  ;; ---------------------------------------------------------------
  ;; Main entry point
  ;; ---------------------------------------------------------------

  ;; check-termination : (list-of expr) x type-env -> (list-of termination-violation)
  ;; Analyzes expressions for potential non-termination.
  (define (check-termination exprs type-env)
    (append (analyze-do-forms exprs)
            (analyze-named-let-forms exprs)))
)
