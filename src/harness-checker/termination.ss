;; termination.ss
;; Termination analysis pass for the harness checker.
;; Detects programs that may not terminate (infinite loops / unbounded recursion).
;;
;; Phase 1 (scaffolding): stub returning empty list for all inputs.
;; Phase 2 (call graph): build directed call graph from top-level definitions
;;   and identify strongly connected components (SCCs) for recursion analysis.
;; Phase 3 (do-form analysis): analyze do-loop constructs for termination by
;;   verifying exit conditions and step expressions.

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
          analyze-do-forms)
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
  ;; Main entry point
  ;; ---------------------------------------------------------------

  ;; check-termination : (list-of expr) x type-env -> (list-of termination-violation)
  ;; Analyzes expressions for potential non-termination.
  (define (check-termination exprs type-env)
    (analyze-do-forms exprs))
)
