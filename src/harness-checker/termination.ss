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
          ;; HC-2: higher-order call edges from 0CFA
          cfa-rewrite-program
          ;; Collection HOF whitelist
          collection-hof?
          ;; HOF callback analysis
          hof-callback-position
          collect-hof-callback-edges
          collect-user-hof-callback-edges
          detect-user-defined-hofs
          check-hof-callbacks
          ;; Type-env lookup
          type-env-lookup)
  (import (rnrs)
          (only (chezscheme) top-level-bound? top-level-syntax? scheme-environment gensym)
          (harness-checker types)
          (harness-checker cfa)
          (harness-checker sct))

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

  ;; Mapping from each collection HOF to the zero-based positional index
  ;; of its callback argument, or #f if it takes no callback.
  ;;
  ;; The collection-hof-names whitelist vouches for the *iteration mechanism*
  ;; terminating (bounded by collection size). Callback termination is checked
  ;; separately by check-hof-callbacks, which runs after SCC analysis.
  ;; Inline lambdas are covered by normal collect-calls-in-body traversal;
  ;; collect-hof-callback-edges handles symbol references only.
  ;; Functions not in the user-defined set are assumed safe (not the
  ;; responsibility of this check).
  (define collection-hof-callback-position
    '((map . 0) (for-each . 0) (filter . 0) (remove . 0)
      (remp . 0) (remv . #f) (remq . #f)
      (fold-left . 0) (fold-right . 0)
      (find . 0) (exists . 0) (for-all . 0) (memp . 0)
      (memv . #f) (memq . #f)
      (assoc . #f) (assv . #f) (assq . #f)
      (vector-map . 0) (vector-for-each . 0) (string-for-each . 0)))

  ;; Look up the callback position for a HOF. Returns the zero-based
  ;; index or #f if the HOF takes no callback argument.
  (define (hof-callback-position sym)
    (let ((entry (assq sym collection-hof-callback-position)))
      (and entry (cdr entry))))

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
  ;;   letrec/letrec* bindings with lambda or case-lambda values
  ;; Recursively processes body expressions to find internal defines.
  ;; Returns alist of (name . body-exprs)
  (define (extract-definitions exprs)
    (let ((defs '()))
      (define (process-expr expr)
        ;; Quoted data, dotted or not, is never code (HC-2 round 11, I1).
        (when (and (pair? expr) (list? expr) (not (eq? (car expr) 'quote)))
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
                           (memq (car (cadr binding)) '(lambda case-lambda))
                           (pair? (cdr (cadr binding))))
                  (let ((name (car binding))
                        (body (if (eq? (car (cadr binding)) 'lambda)
                                  (cddr (cadr binding))
                                  (apply append
                                         (map (lambda (c) (if (pair? c) (cdr c) '()))
                                              (cdr (cadr binding)))))))
                    (set! defs (cons (cons name body) defs))
                    ;; Recurse into body to find internal defines
                    (for-each process-expr body)))
                ;; Any other init may hold one, as cfa-rewrite-program
                ;; wraps anonymous lambdas in letrec wherever they sit.
                (when (and (pair? binding) (pair? (cdr binding))
                           (not (and (pair? (cadr binding))
                                     (memq (car (cadr binding)) '(lambda case-lambda)))))
                  (process-expr (cadr binding))))
              (cadr expr))
             ;; Also recurse into the letrec body expressions
             (for-each process-expr (cddr expr)))

            ;; For other compound expressions, recurse to find nested
            ;; defines, operator included: ((letrec ((lp ...)) lp) 1).
            (else
             (for-each
              (lambda (sub)
                (when (pair? sub)
                  (process-expr sub)))
              expr)))))

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

  ;; Collect HOF callback edges from body expressions.
  ;; For each application where (car expr) is a collection-hof with a
  ;; non-#f callback position, extract the callback argument. If it is
  ;; a symbol, record it as a HOF callback edge (caller-name . callback-symbol).
  ;; Inline lambdas are skipped — they are already handled by normal
  ;; collect-calls-in-body traversal which recurses into (cdr expr).
  (define (collect-hof-callback-edges body-exprs caller-name)
    (let ((edges '()))
      (define (walk expr)
        (when (pair? expr)
          (unless (eq? (car expr) 'quote)
            (when (and (symbol? (car expr)) (collection-hof? (car expr)))
              (let ((cb-pos (hof-callback-position (car expr))))
                (when cb-pos
                  (let ((args (cdr expr)))
                    (when (> (length args) cb-pos)
                      (let ((cb-arg (list-ref args cb-pos)))
                        (when (symbol? cb-arg)
                          (set! edges (cons (cons caller-name cb-arg) edges)))))))))
            (for-each walk (cdr expr))
            (when (pair? (car expr))
              (walk (car expr))))))
      (for-each walk body-exprs)
      edges))

  ;; Collect user-defined HOF callback edges from body expressions.
  ;; user-hof-table: alist of ((hof-name . callback-position) ...)
  ;; Returns list of (caller-name hof-name callback-symbol) triples,
  ;; where hof-name identifies which user-defined HOF was called.
  (define (collect-user-hof-callback-edges body-exprs caller-name user-hof-table)
    (let ((edges '()))
      (define (walk expr)
        (when (pair? expr)
          (unless (eq? (car expr) 'quote)
            (when (symbol? (car expr))
              (let ((entry (assq (car expr) user-hof-table)))
                (when entry
                  (let ((cb-pos (cdr entry))
                        (args (cdr expr)))
                    (when (> (length args) cb-pos)
                      (let ((cb-arg (list-ref args cb-pos)))
                        (when (symbol? cb-arg)
                          (set! edges (cons (list caller-name (car expr) cb-arg) edges)))))))))
            (for-each walk (cdr expr))
            (when (pair? (car expr))
              (walk (car expr))))))
      (for-each walk body-exprs)
      edges))

  ;; Check if a symbol appears in call position (car of a non-quoted
  ;; application) within body expressions.
  (define (param-in-call-position? sym body-exprs)
    (let ((found #f))
      (define (walk expr)
        (when (and (not found) (pair? expr))
          (unless (eq? (car expr) 'quote)
            (when (eq? (car expr) sym)
              (set! found #t))
            (when (pair? (car expr))
              (walk (car expr)))
            (for-each walk (cdr expr)))))
      (for-each walk body-exprs)
      found))

  ;; Detect user-defined higher-order functions by checking if any
  ;; formal parameter appears in call position within the function body.
  ;; defs: alist of (name . body-exprs) from extract-definitions.
  ;; exprs: original expression list (for extracting formals).
  ;; Returns alist of ((fn-name . callback-position) ...) where
  ;; callback-position is the zero-based index of the first formal
  ;; that appears in call position. Functions already in the built-in
  ;; collection-hof whitelist are excluded.
  (define (detect-user-defined-hofs defs exprs)
    (let ((result '()))
      (for-each
        (lambda (def)
          (let* ((name (car def))
                 (body (cdr def))
                 (formals (find-formals-for exprs name)))
            (when (and formals (pair? formals)
                       (not (collection-hof? name)))
              (let loop ((fs formals) (pos 0))
                (unless (or (null? fs) (assq name result))
                  (when (and (symbol? (car fs))
                             (param-in-call-position? (car fs) body))
                    (set! result (cons (cons name pos) result)))
                  (loop (cdr fs) (+ pos 1)))))))
        defs)
      (reverse result)))

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
  ;; Phase 2b: higher-order call edges from 0CFA (HC-2)
  ;; ---------------------------------------------------------------
  ;;
  ;; build-call-graph sees a call only when its operator names a
  ;; definition. cfa-rewrite-program makes every other call visible to it,
  ;; and to the Phase 5/6 checks, by rewriting the program: at each call
  ;; site where 0CFA finds a lambda the name lookup misses, it inserts a
  ;; synthesized call to that lambda's owner, in place, so the decreasing
  ;; and base-case checks see it in its real branch.
  ;;
  ;; The owner of a lambda is the nearest enclosing define or letrec
  ;; binding. An anonymous lambda with none owns itself; it is wrapped as
  ;; (letrec ((lambda@N <lambda>)) lambda@N) so it becomes a definition.
  ;; A call into an anonymous lambda owned by the caller is a nested helper
  ;; and adds no edge. See plans/hc-0cfa.md in the overlord vault.
  ;;
  ;; The rewritten program is for analysis only and is never run.

  ;; Head of the synthesized argument meaning "an element of this list".
  ;; decreasing-expr? accepts it. It is not on the whitelist, so no
  ;; checked program can contain it.
  (define cfa-element-marker '%cfa-element)
  ;; An element of apply's trailing list. It descends like
  ;; %cfa-element, but apply calls its procedure once, so the call is
  ;; not a per-element callback (HC-2 round 10, I3).
  (define cfa-spread-marker '%cfa-spread)

  (define (cfa-element-form? expr)
    (and (pair? expr)
         (memq (car expr) (list cfa-element-marker cfa-spread-marker))
         #t))

  ;; List HOFs whose callback receives list elements. Vector and string
  ;; HOFs are left out: vector-set! can make a vector contain itself.
  (define cfa-list-hof-names
    '(map for-each filter remove remp fold-left fold-right find exists
      for-all memp partition))

  ;; The synthesized arguments of a built-in HOF's callback invocation at
  ;; site expression e, for a callback with n formals. Position i gets
  ;; (%cfa-element <list>) when it receives elements of a syntactic list
  ;; argument, else #f, which decreases nothing.
  ;; name is the HOF built-in 0CFA resolved the operator to. The site's
  ;; arguments are trusted only when its head is that same name, so a
  ;; rebinding such as (let ((map fold-left)) ...) proves nothing.
  (define (cfa-hof-callback-args e name n)
    (let* ((h (and (list? e) (pair? e) (car e)))
           (args (if (and h name (eq? h name) (memq h cfa-list-hof-names))
                     (cdr e)
                     #f)))
      (define (element-of k)
        (if (and args (< k (length args)))
            (list cfa-element-marker (list-ref args k))
            #f))
      (let loop ((i 0) (acc '()))
        (if (= i n)
            (reverse acc)
            (loop (+ i 1)
                  (cons (cond
                          ((not args) #f)
                          ;; (fold-left f init l ...): callback gets (acc e ...)
                          ((eq? h 'fold-left) (if (= i 0) #f (element-of (+ i 1))))
                          ;; (fold-right f init l ...): callback gets (e ... acc)
                          ((eq? h 'fold-right)
                           (if (< (+ i 2) (length args)) (element-of (+ i 2)) #f))
                          (else (element-of (+ i 1))))
                        acc))))))

  ;; (apply f a ... lst): leading arguments positionally, then elements
  ;; of lst for the remaining formals.
  (define (cfa-apply-args e n)
    (if (and (list? e) (>= (length e) 3))
        (let* ((more (cddr e))
               (lst (list-ref more (- (length more) 1)))
               (leading (let take ((m more))
                          (if (null? (cdr m)) '() (cons (car m) (take (cdr m)))))))
          (let loop ((i 0) (ls leading) (acc '()))
            (if (= i n)
                (reverse acc)
                (if (pair? ls)
                    (loop (+ i 1) (cdr ls) (cons (car ls) acc))
                    (loop (+ i 1) ls (cons (list cfa-spread-marker lst) acc))))))
        '()))

  (define (cfa-anon-node-name label)
    (string->symbol (string-append "lambda@" (number->string label))))

  (define (cfa-rewrite-program exprs)
    (let-values (((rewritten violations) (cfa-analyze-program exprs)))
      rewritten))

  ;; Returns two values: the rewritten program, and the violations 0CFA
  ;; finds that the rewrite cannot express. Those are call sites whose
  ;; operator 0CFA cannot follow (unresolved-call), and cycles made only of
  ;; anonymous lambdas, which have no definition to carry a call edge.
  (define (cfa-analyze-program exprs)
    (let* ((result (cfa-analyze exprs))
           (site-synth (make-eq-hashtable))
           (wrap (make-eq-hashtable)))

      (define (lam label) (cfa-lambda-ref result label))

      (define (named? l) (and (memq (cfa-lambda-kind l) '(define letrec)) #t))

      (define (named-owner label)
        (and label
             (let ((l (lam label)))
               (if (named? l)
                   (cfa-lambda-name l)
                   (named-owner (cfa-lambda-parent l))))))

      ;; An anonymous lambda can own itself only when its source is a
      ;; lambda form we can wrap.
      (define (anon-node? label)
        (let ((l (lam label)))
          (and (eq? (cfa-lambda-kind l) 'lambda)
               (not (named-owner label))
               (let ((src (cfa-lambda-expr l)))
                 (and (pair? src) (eq? (car src) 'lambda))))))

      (define (node-lambda? label)
        (or (named? (lam label)) (anon-node? label)))

      ;; Owner node name, or #f for top-level code and top-level named lets.
      ;; A named let runs inside the lambda that encloses it, so it shares
      ;; that lambda's owner, anonymous node included (HC-2 round 10, I4).
      (define (owner label)
        (and label
             (or (named-owner label)
                 (and (anon-node? label)
                      (begin
                        (hashtable-set! wrap (cfa-lambda-expr (lam label))
                                        (cfa-anon-node-name label))
                        (cfa-anon-node-name label)))
                 (and (eq? (cfa-lambda-kind (lam label)) 'named-let)
                      (owner (cfa-lambda-parent (lam label)))))))

      ;; A lambda is a leaf when no call site inside it, at any depth,
      ;; can invoke a lambda. Calling a leaf cannot re-enter any
      ;; definition, so it adds no edge.
      (define (inside? label ancestor)
        (and label
             (or (= label ancestor)
                 (inside? (cfa-lambda-parent (lam label)) ancestor))))

      (define (leaf-lambda? label)
        (not (exists (lambda (site)
                       (and (inside? (cfa-site-caller site) label)
                            (or (pair? (cfa-site-callees site))
                                (cfa-site-unresolved? site))))
                     (cfa-result-sites result))))

      (define (synth-args e via l)
        (let ((n (length (cfa-lambda-formals l))))
          (cond
            ((and (pair? via) (eq? (car via) 'hof))
             (cfa-hof-callback-args e (cdr via) n))
            ((eq? via 'direct) (if (list? e) (cdr e) '()))
            ((eq? via 'cond-arrow) (list (car e)))
            ((eq? via 'apply) (cfa-apply-args e n))
            (else '()))))

      (define (synth-calls site)
        (let ((e (cfa-site-expr site))
              (from (owner (cfa-site-caller site))))
          (if (not from)
              '()
              (fold-left
                (lambda (acc entry)
                  (let* ((label (car entry))
                         (via (cdr entry))
                         (to (owner label))
                         (call
                           (cond
                             ((not to) #f)
                             ;; A nested helper of the caller: intraprocedural.
                             ((and (not (node-lambda? label)) (eq? to from)) #f)
                             ((and (not (node-lambda? label)) (leaf-lambda? label)) #f)
                             ;; A lambda inside another definition: an edge
                             ;; to that owner whose arguments prove nothing.
                             ((not (node-lambda? label)) (list to))
                             ;; Already a call by name.
                             ((and (eq? via 'direct) (pair? e) (eq? (car e) to)) #f)
                             (else (cons to (synth-args e via (lam label)))))))
                    (if (and call (not (member call acc)))
                        (cons call acc)
                        acc)))
                '()
                (cfa-site-callees site)))))

      (define (cond-arrow-clause? e)
        (and (list? e) (= (length e) 3) (eq? (cadr e) '=>)))

      (define (rw e)
        (if (or (not (pair? e)) (eq? (car e) 'quote))
            e
            (let* ((e2 (rw-list e))
                   (synth (hashtable-ref site-synth e #f))
                   (e3 (cond
                         ((not synth) e2)
                         ((cond-arrow-clause? e) (append e2 (reverse synth)))
                         (else (cons 'begin (cons e2 (reverse synth))))))
                   (w (hashtable-ref wrap e #f)))
              (if w
                  (list 'letrec (list (list w e3)) w)
                  e3))))

      (define (rw-list e)
        (if (pair? e)
            (cons (rw (car e)) (rw-list (cdr e)))
            e))

      ;; A call site whose operator set can hold a value 0CFA cannot follow.
      (define (unresolved-violations)
        (fold-left
          (lambda (acc site)
            (if (cfa-site-unresolved? site)
                (cons (make-termination-violation
                        'unresolved-call
                        (owner (cfa-site-caller site))
                        (cfa-site-expr site)
                        "operator may be a value the control-flow analysis cannot follow")
                      acc)
                acc))
          '()
          (cfa-result-sites result)))

      ;; A call from a definition into a lambda that has no owner: a
      ;; top-level case-lambda clause or named let. No edge can be drawn
      ;; to it, so unless it is a leaf it may call back into the caller
      ;; unseen, and the call fails closed.
      (define (unowned-callee-violations)
        (fold-left
          (lambda (acc site)
            (let ((from (owner (cfa-site-caller site))))
              (if (and from
                       (exists (lambda (entry)
                                 (and (not (owner (car entry)))
                                      (not (leaf-lambda? (car entry)))))
                               (cfa-site-callees site)))
                  (cons (make-termination-violation
                          'unresolved-call
                          from
                          (cfa-site-expr site)
                          "calls a top-level case-lambda clause or named let that may call back")
                        acc)
                  acc)))
          '()
          (cfa-result-sites result)))

      ;; Anonymous lambdas that no rewrite turns into a definition: those
      ;; nested in a definition, and top-level case-lambda clauses. Calls
      ;; among them carry no edge in the definition graph, so a cycle made
      ;; only of them is checked here, on the lambda-level graph, with the
      ;; same size-change check as definition SCCs.
      (define (anon-member? label)
        (let ((l (lam label)))
          (and (eq? (cfa-lambda-kind l) 'lambda)
               (not (anon-node? label)))))

      ;; A named let's body runs inside the lambda that encloses it, so a
      ;; call made from a named let is a call by that lambda. Its own loop
      ;; calls are Phase 4's; calls out of it must not drop off the graph.
      (define (effective-caller label)
        (and label
             (if (eq? (cfa-lambda-kind (lam label)) 'named-let)
                 (effective-caller (cfa-lambda-parent (lam label)))
                 label)))

      (define (anon-cycle-violations)
        (let* ((edges
                 ;; (caller callee site) among anonymous lambdas of one owner
                 (fold-left
                   (lambda (acc site)
                     (let ((c (effective-caller (cfa-site-caller site))))
                       (if (and c (anon-member? c))
                           (fold-left
                             (lambda (acc entry)
                               (let ((b (car entry)))
                                 (if (and (anon-member? b)
                                          (eq? (named-owner b) (named-owner c)))
                                     (cons (list c b site entry) acc)
                                     acc)))
                             acc
                             (cfa-site-callees site))
                           acc)))
                   '()
                   (cfa-result-sites result)))
               (succ (make-eqv-hashtable))
               (graph
                 (begin
                   (for-each
                     (lambda (e)
                       (let ((ss (hashtable-ref succ (car e) '())))
                         (unless (memv (cadr e) ss)
                           (hashtable-set! succ (car e) (cons (cadr e) ss)))))
                     edges)
                   (let-values (((keys vals) (hashtable-entries succ)))
                     (map cons (vector->list keys) (vector->list vals)))))
               (sccs (tarjan-scc graph)))
          (define (scc-of label)
            (find (lambda (scc) (memv label scc)) sccs))
          (define (in-cycle? e)
            (let ((scc (scc-of (car e))))
              (and scc
                   (memv (cadr e) scc)
                   (or (> (length scc) 1) (= (car e) (cadr e))))))
          ;; The size-change graph of one intra-cycle call. An argument
          ;; that mentions a name rebound around the call site proves
          ;; nothing, nor does any argument when the site is not found.
          (define (edge-sc-graph numeric-strict? e)
            (let* ((caller (lam (car e)))
                   (site-expr (cfa-site-expr (caddr e)))
                   (shadowed (names-shadowed-at (cfa-lambda-body caller) site-expr))
                   (args (map (lambda (a)
                                (if (and shadowed (not (expr-references-any? a shadowed)))
                                    a
                                    #f))
                              (synth-args site-expr (cdr (cadddr e)) (lam (cadr e))))))
              (call-sc-graph (car e)
                             (unassigned-formals (cfa-lambda-formals caller)
                                                 (cfa-lambda-body caller))
                             '() '()
                             (cons (cadr e) args)
                             (cfa-lambda-formals (lam (cadr e)))
                             numeric-strict?)))
          ;; Numeric descent stops only at a base-case test, so every cycle
          ;; needs a member with a branch, guarded by a test on its formals,
          ;; that makes none of the cycle's calls (HC-2 round 10 I1, round 11 C3).
          (define (scc-base-case? scc es)
            (let ((sites (map (lambda (e) (cfa-site-expr (caddr e))) es)))
              (define (calls-cycle? x)
                (or (and (memq x sites) #t)
                    (and (pair? x)
                         (not (eq? (car x) 'quote))
                         (or (calls-cycle? (car x)) (calls-cycle? (cdr x))))))
              (let ((unbased
                      (filter (lambda (label)
                                (let ((l (lam label)))
                                  (not (has-base-case-by? (cfa-lambda-body l)
                                                          (cfa-lambda-formals l)
                                                          '()
                                                          calls-cycle?))))
                              scc)))
                (acyclic? unbased
                          (lambda (label)
                            (filter (lambda (c) (memv c unbased))
                                    (map cadr (filter (lambda (e) (eqv? (car e) label))
                                                      es))))))))
          ;; Each cyclic SCC must pass the size-change check, like a
          ;; definition SCC in Phases 5/6, and have a base case.
          (fold-left
            (lambda (acc scc)
              (let ((es (filter (lambda (e) (and (in-cycle? e) (memv (car e) scc))) edges)))
                (if (null? es)
                    acc
                    (let* ((e (car es))
                           (progress (sc-check-members
                                       (lambda (numeric-strict?)
                                         (map (lambda (e) (edge-sc-graph numeric-strict? e)) es))
                                       (length scc)))
                           (progress (if (and (eq? progress 'terminates)
                                              (not (scc-base-case? scc es)))
                                         'no-base-case
                                         progress)))
                      (if (eq? progress 'terminates)
                          acc
                          (cons (make-termination-violation
                                  (case progress
                                    ((limit) 'size-change-limit)
                                    ((no-base-case) 'no-base-case)
                                    (else 'no-decreasing-arg))
                                  (or (named-owner (car e)) (cfa-anon-node-name (car e)))
                                  (cfa-site-expr (caddr e))
                                  (if (eq? progress 'no-base-case)
                                      "anonymous lambda recursion with no base case"
                                      "anonymous lambda recursion with no decreasing argument"))
                                acc))))))
            '()
            sccs)))

      ;; Phase 4 sees a named let's recursion only as calls by its name.
      ;; Any other call into a named let that can call a lambda, through an
      ;; alias, a HOF or apply, may re-enter the loop unseen, so it fails
      ;; closed.
      (define (named-let-alias-violations)
        (fold-left
          (lambda (acc site)
            (let ((e (cfa-site-expr site)))
              (fold-left
                (lambda (acc entry)
                  (let* ((label (car entry))
                         (via (cdr entry))
                         (l (lam label)))
                    (if (and (eq? (cfa-lambda-kind l) 'named-let)
                             (not (memq via '(named-let escape)))
                             (not (and (eq? via 'direct)
                                       (pair? e)
                                       (eq? (car e) (cfa-lambda-name l))))
                             (not (leaf-lambda? label)))
                        (cons (make-termination-violation
                                'named-let-alias
                                (owner (cfa-site-caller site))
                                e
                                (string-append "named-let \""
                                               (symbol->string (cfa-lambda-name l))
                                               "\" called other than by its name"))
                              acc)
                        acc)))
                acc
                (cfa-site-callees site))))
          '()
          (cfa-result-sites result)))

      (for-each
        (lambda (site)
          (let ((calls (synth-calls site)))
            (unless (null? calls)
              (hashtable-set! site-synth (cfa-site-expr site) calls))))
        (cfa-result-sites result))

      (let ((violations (append (unresolved-violations)
                                (unowned-callee-violations)
                                (anon-cycle-violations)
                                (named-let-alias-violations))))
        (values (if (= (hashtable-size site-synth) 0)
                    exprs
                    (map rw exprs))
                violations))))

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
                   (null? (cdddr expr))
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
                   (null? (cdddr expr))
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
              ;; (%cfa-element coll): an element of list coll, handed to a
              ;; HOF callback (HC-2). It decreases var when coll is var or
              ;; a decreasing expression of var. Lists are acyclic because
              ;; set-car!/set-cdr! are not whitelisted.
              (and (cfa-element-form? expr)
                   (pair? (cdr expr))
                   (or (eq? (cadr expr) var)
                       (decreasing-expr? (cadr expr) var var-type)))
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
                       (null? (cdddr expr))
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
                       (null? (cdddr expr))
                       (number? (caddr expr))
                       (> (caddr expr) 0))))))))

  ;; Check if an expression is strictly increasing for the given variable.
  ;; Increasing: (+ x 1), (add1 x), (fx+ x 1)
  (define (increasing-expr? expr var)
    (and (pair? expr)
         (or
           ;; (+ var <positive>) or (+ <positive> var)
           (and (eq? (car expr) '+)
                (pair? (cdr expr))
                (pair? (cddr expr))
                (null? (cdddr expr))
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
                (null? (cdddr expr))
                (number? (caddr expr))
                (> (caddr expr) 0)))))

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
              ;; (>= var N) where var reached or passed upper bound
              (and (eq? (car expr) '>=)
                   (pair? (cdr expr))
                   (pair? (cddr expr))
                   (memq (cadr expr) vars)
                   (not (memq (caddr expr) vars)))
              ;; (> var N) where var exceeded upper bound
              (and (eq? (car expr) '>)
                   (pair? (cdr expr))
                   (pair? (cddr expr))
                   (memq (cadr expr) vars)
                   (not (memq (caddr expr) vars)))
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

  ;; A test whose FALSE branch is a base case: (pair? var), or (not T)
  ;; where T is a base-case test.
  (define (negated-base-case-test? expr vars type-env)
    (and (pair? expr)
         (pair? (cdr expr))
         (null? (cddr expr))
         (or (and (eq? (car expr) 'pair?)
                  (memq (cadr expr) vars)
                  #t)
             (and (eq? (car expr) 'not)
                  (base-case-test? (cadr expr) vars type-env)))))

  ;; Check if an expression is an upper-bound base-case test for the given
  ;; variables. These are tests where termination requires the variable to
  ;; INCREASE toward the bound: (>= var N), (> var N), (= var N) where N
  ;; is not zero/null. Used to pair with increasing-expr? for soundness.
  (define (upper-bound-base-case-test? expr vars)
    (and (pair? expr)
         (or
           ;; (>= var N) where var is a loop variable, N is not
           (and (eq? (car expr) '>=)
                (pair? (cdr expr))
                (pair? (cddr expr))
                (memq (cadr expr) vars)
                (not (memq (caddr expr) vars)))
           ;; (> var N) where var is a loop variable, N is not
           (and (eq? (car expr) '>)
                (pair? (cdr expr))
                (pair? (cddr expr))
                (memq (cadr expr) vars)
                (not (memq (caddr expr) vars)))
           ;; (= var N) where N is not a loop variable and not literal 0
           (and (eq? (car expr) '=)
                (pair? (cdr expr))
                (pair? (cddr expr))
                (or (and (memq (cadr expr) vars)
                         (not (memq (caddr expr) vars))
                         (not (eqv? (caddr expr) 0)))
                    (and (not (memq (cadr expr) vars))
                         (not (eqv? (cadr expr) 0))
                         (memq (caddr expr) vars)))))))

  ;; The (var . bound) pair an upper-bound base-case test constrains.
  (define (upper-bound-test-pair test vars)
    (if (and (eq? (car test) '=) (not (memq (cadr test) vars)))
        (cons (caddr test) (cadr test))
        (cons (cadr test) (caddr test))))

  ;; The (var . bound) pairs of the body's upper-bound base cases -- a
  ;; conditional branch with an upper-bound test that does not contain a
  ;; recursive call. Mirrors has-base-case? but only accepts upper-bound
  ;; patterns. when is not one: its body runs when the test holds, so its
  ;; base case is the test failing (HC-2 round 15).
  (define (upper-bound-base-cases body-exprs loop-name vars)
    (let ((found '()))
      (define (note! test)
        (set! found (cons (upper-bound-test-pair test vars) found)))
      (define (walk expr)
        (when (pair? expr)
          (unless (eq? (car expr) 'quote)
            (cond
              ;; (if test consequent alternative)
              ((eq? (car expr) 'if)
               (when (and (pair? (cdr expr)) (pair? (cddr expr)))
                 (let ((test (cadr expr))
                       (consequent (caddr expr)))
                   (when (and (upper-bound-base-case-test? test vars)
                              (not (contains-call? consequent loop-name)))
                     (note! test))
                   (walk consequent)
                   (when (pair? (cdddr expr)) (walk (cadddr expr))))))
              ;; (cond clauses...)
              ((eq? (car expr) 'cond)
               (for-each
                 (lambda (clause)
                   (when (and (pair? clause) (pair? (cdr clause)))
                     (let ((test (car clause)))
                       (when (and (upper-bound-base-case-test? test vars)
                                  (not (contains-call? (cdr clause) loop-name)))
                         (note! test)))))
                 (cdr expr)))
              ;; (unless test body...) -- base case is when test is true
              ((eq? (car expr) 'unless)
               (when (and (pair? (cdr expr))
                          (upper-bound-base-case-test? (cadr expr) vars))
                 (note! (cadr expr))))
              (else
               (when (pair? (car expr)) (walk (car expr)))
               (for-each (lambda (sub) (when (pair? sub) (walk sub)))
                         (cdr expr)))))))
      (for-each walk body-exprs)
      found))

  ;; Check if the body has a base case -- a conditional branch that does
  ;; not contain a recursive call to loop-name.
  ;; Looks for if/cond/when/unless guards.
  ;; type-env is optional (defaults to '()).
  (define has-base-case?
    (case-lambda
      ((body-exprs loop-name vars)
       (has-base-case? body-exprs loop-name vars '()))
      ((body-exprs loop-name vars type-env)
       (has-base-case-by? body-exprs vars type-env
                          (lambda (e) (contains-call? e loop-name))))))

  ;; has-base-case?, with calls? deciding whether an expression can
  ;; recurse. The anonymous-cycle check passes one that looks for its
  ;; cycle's call sites, which have no name (HC-2 round 10, I1).
  (define (has-base-case-by? body-exprs vars type-env calls?)
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
                                 (not (calls? consequent)))
                        (set! found #t))
                      ;; Or the test negates a base-case test and the
                      ;; alternative doesn't recurse: (if (pair? x) <rec> <base>)
                      (when (and alternative
                                 (negated-base-case-test? test vars type-env)
                                 (not (calls? alternative)))
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
                                     (not (calls? body)))
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
                      (when (and (calls? body)
                                 (not (calls? test))
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
                      (when (and (calls? body)
                                 (not (calls? test))
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
  ;; type-env: global type-env (defaults to '()).
  ;; param-types: per-function parameter type alist (defaults to '()).
  ;;   When a named-let is found inside a function definition, the enclosing
  ;;   function's parameter bindings are prepended to type-env for analysis.
  ;; Returns a list of termination-violation records.
  (define analyze-named-let-forms
    (case-lambda
      ((exprs) (analyze-named-let-forms exprs '() '()))
      ((exprs type-env) (analyze-named-let-forms exprs type-env '()))
      ((exprs type-env param-types)
       (let ((violations '()))
         (define (add-violation! kind loop-name expr reason)
           (set! violations
             (cons (make-termination-violation kind loop-name expr reason)
                   violations)))

         ;; Walk expressions, tracking current scoped type-env.
         ;; When entering a function definition, extend the env with
         ;; that function's parameter types from param-types.
         (define (walk expr current-env)
           (when (pair? expr)
             (unless (eq? (car expr) 'quote)
               (cond
                 ;; (define (name params...) body...) — scope param-types
                 ((and (eq? (car expr) 'define)
                       (pair? (cdr expr))
                       (pair? (cadr expr))
                       (symbol? (caadr expr)))
                  (let* ((name (caadr expr))
                         (fn-params (assq name param-types))
                         (scoped-env (if fn-params
                                        (append (cdr fn-params) type-env)
                                        current-env)))
                    (for-each (lambda (sub) (walk sub scoped-env)) (cddr expr))))

                 ;; (define name (lambda (params...) body...)) — scope param-types
                 ((and (eq? (car expr) 'define)
                       (pair? (cdr expr))
                       (symbol? (cadr expr))
                       (pair? (cddr expr))
                       (pair? (caddr expr))
                       (eq? (car (caddr expr)) 'lambda)
                       (pair? (cdr (caddr expr))))
                  (let* ((name (cadr expr))
                         (fn-params (assq name param-types))
                         (scoped-env (if fn-params
                                        (append (cdr fn-params) type-env)
                                        current-env)))
                    (for-each (lambda (sub) (walk sub scoped-env)) (cddr (caddr expr)))))

                 ;; Named-let: analyze with current scoped env
                 ((and (eq? (car expr) 'let)
                       (pair? (cdr expr))
                       (symbol? (cadr expr))
                       (pair? (cddr expr))
                       (pair? (cdddr expr)))
                  (check-named-let expr current-env)
                  ;; Continue walking sub-expressions
                  (when (pair? (car expr))
                    (walk (car expr) current-env))
                  (for-each (lambda (sub) (when (pair? sub) (walk sub current-env)))
                            (cdr expr)))

                 ;; Generic: recurse into sub-expressions
                 (else
                  (when (pair? (car expr))
                    (walk (car expr) current-env))
                  (for-each (lambda (sub) (when (pair? sub) (walk sub current-env)))
                            (cdr expr)))))))

         ;; Every call to loop-name in its body has a monotonic argument.
         ;; A call inside a closure that may run in a later iteration has
         ;; only #f arguments, as in Phases 5 and 6.
         (define (named-let-calls-decrease? expr loop-name vars env)
           (let ((calls (collect-intra-scc-calls
                          (cdddr expr) (list loop-name)
                          (append (cons loop-name (binding-names (caddr expr)))
                                  (or (names-shadowed-at exprs expr) '())))))
             (and (pair? calls)
                  (for-all
                    (lambda (call)
                      (let check ((args (cdr call)) (params vars))
                        (and (pair? args) (pair? params)
                             (or (and (car args)
                                      (monotonic-expr? (car args) (car params)
                                        (type-env-lookup env (car params))))
                                 (check (cdr args) (cdr params))))))
                    calls))))

         (define (check-named-let expr current-env)
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
                      (not (named-let-calls-decrease? expr loop-name vars current-env)))
                  (add-violation! 'no-decreasing-arg loop-name expr
                    (string-append "named-let \"" (symbol->string loop-name)
                      "\" has no decreasing argument in recursive call(s)")))

                 ;; Has decreasing args but no base case
                 ((not (has-base-case? body loop-name vars current-env))
                  (add-violation! 'no-base-case loop-name expr
                    (string-append "named-let \"" (symbol->string loop-name)
                      "\" has no reachable base case")))))))

         (for-each (lambda (expr) (walk expr type-env)) exprs)
         (reverse violations)))))

  ;; ---------------------------------------------------------------
  ;; Phases 5 and 6: size-change termination (HC-2)
  ;; ---------------------------------------------------------------
  ;;
  ;; Each intra-SCC call gets a size-change graph (see sct.ss) with an arc
  ;; from caller formal x to callee formal y when the argument passed for
  ;; y is no larger than x: strict when it is a decreasing-expr? of x,
  ;; non-strict when it is x itself. In a single-function SCC, the measure
  ;; "bound minus x" also gets arcs for each formal x that bounded-formals
  ;; accepts: strict when the argument is an increasing-expr? of x. An SCC
  ;; passes when sc-check finds descent round every cycle.
  ;;
  ;; Structural descent (cdr, car, an element) is well-founded, so its arcs
  ;; may cross argument positions. Numeric descent and ascent are bounded
  ;; only by a base-case test on that parameter, so their arcs are kept
  ;; only when x and y sit in the same position, the trust the per-edge
  ;; rule gave them. Without that, (f y (- x 1)) under (= x 0) would pass
  ;; by swapping a negative x out from under its test.

  (define size-change-cap 1000)

  ;; decreasing-expr?, plus (car e) where e is var or decreases var. Pairs
  ;; are immutable here (set-car!/set-cdr! are not whitelisted), so car,
  ;; like cdr, shrinks the longest car/cdr path from a value. Size-change
  ;; arcs only; named-let analysis keeps decreasing-expr?.
  (define (sc-decreasing-expr? expr var var-type)
    (or (decreasing-expr? expr var var-type)
        (and (pair? expr)
             (eq? (car expr) 'car)
             (pair? (cdr expr))
             (null? (cddr expr))
             (or (eq? (cadr expr) var)
                 (sc-decreasing-expr? (cadr expr) var var-type)))))

  (define (bound-measure x) (cons 'bound x))

  ;; Every symbol that is the target of a set! in expr. Shadowing is
  ;; ignored, which only drops more arcs.
  (define (set!-targets expr)
    (cond
      ((not (pair? expr)) '())
      ((eq? (car expr) 'quote) '())
      ((and (eq? (car expr) 'set!) (pair? (cdr expr)) (symbol? (cadr expr)))
       (cons (cadr expr) (set!-targets (cddr expr))))
      (else (append (set!-targets (car expr)) (set!-targets (cdr expr))))))

  ;; formals with each one that body assigns replaced by a fresh symbol,
  ;; keeping positions. An assigned formal no longer holds the value it
  ;; was called with, so no size-change arc may start from it (HC-2
  ;; round 7, C3).
  (define (unassigned-formals formals body)
    (let ((targets (set!-targets body)))
      (map (lambda (x) (if (memq x targets) (gensym) x)) formals)))

  ;; The proper prefix of a formals list; rest arguments get no arcs.
  (define (proper-formals formals)
    (if (pair? formals)
        (cons (car formals) (proper-formals (cdr formals)))
        '()))

  (define numeric-step-names '(- sub1 fx- + add1 fx+))

  (define (numeric-step? expr)
    (and (pair? expr) (memq (car expr) numeric-step-names) #t))

  ;; numeric-strict?: #f demotes numeric-step arcs to non-strict, leaving
  ;; only structural descent strict. bounded: the formals whose "bound
  ;; minus x" measure gets arcs.
  (define (call-sc-graph caller caller-formals type-env bounded call callee-formals
                         numeric-strict?)
    (make-sc-graph caller (car call)
      (let loop ((args (cdr call)) (params callee-formals) (j 0) (acc '()))
        (if (or (not (pair? args)) (not (pair? params)))
            acc
            (let ((a (car args)) (y (car params)))
              (loop (cdr args) (cdr params) (+ j 1)
                (let xloop ((xs caller-formals) (i 0) (acc acc))
                  (if (null? xs)
                      acc
                      (let* ((x (car xs))
                             (placed? (or (= i j) (not (numeric-step? a)))))
                        (xloop (cdr xs) (+ i 1)
                          (append
                            (cond
                              ((and placed?
                                    (sc-decreasing-expr? a x (type-env-lookup type-env x)))
                               (list (list x y (or numeric-strict? (not (numeric-step? a))))))
                              ((eq? a x) (list (list x y #f)))
                              (else '()))
                            (cond
                              ((not (and (memq x bounded) (memq y bounded))) '())
                              ((and (= i j) (increasing-expr? a x))
                               (list (list (bound-measure x) (bound-measure y) #t)))
                              ((eq? a x)
                               (list (list (bound-measure x) (bound-measure y) #f)))
                              (else '()))
                            acc)))))))))))

  ;; Operators a stable bound may apply: their result is fixed by their
  ;; arguments. vector-ref is not one, since vector-set! can raise it.
  (define pure-bound-ops
    '(length vector-length string-length + - * quotient remainder modulo
      abs min max car cdr cadr cddr))

  ;; The formals x, from the (x . bound) pairs of a self-recursive
  ;; function's upper-bound base cases, whose "bound minus x" measure is
  ;; sound: the bound cannot grow between calls. It may apply only
  ;; pure-bound-ops, every formal it mentions must be passed unchanged in
  ;; place on every recursive call, and no name in it may be assigned
  ;; anywhere (assigned: every set! target in the program). HC-2 round 15
  ;; C1/C2: without this, an unconstrained formal or a growing bound
  ;; such as (length l) under (cons 1 l) carried the measure.
  (define (bounded-formals pairs formals calls assigned)
    (define (in-place? z)
      (let ((i (let loop ((fs formals) (i 0))
                 (cond ((null? fs) #f) ((eq? (car fs) z) i) (else (loop (cdr fs) (+ i 1)))))))
        (for-all (lambda (call)
                   (let loop ((args (cdr call)) (k 0))
                     (and (pair? args)
                          (if (= k i) (eq? (car args) z) (loop (cdr args) (+ k 1))))))
                 calls)))
    (define (stable? e)
      (cond
        ((symbol? e) (and (not (memq e assigned))
                          (or (not (memq e formals)) (in-place? e))))
        ((pair? e) (or (eq? (car e) 'quote)
                       (and (memq (car e) pure-bound-ops)
                            (list? e)
                            (for-all stable? (cdr e)))))
        (else #t)))
    (let loop ((ps pairs) (acc '()))
      (cond
        ((null? ps) acc)
        ((and (memq (caar ps) formals) (not (memq (caar ps) acc)) (stable? (cdar ps)))
         (loop (cdr ps) (cons (caar ps) acc)))
        (else (loop (cdr ps) acc)))))

  ;; 'terminates, 'no-descent or 'limit for the SCC scc-names.
  ;; formals-of, body-of and type-env-of map a member name to its formals
  ;; (or #f), body and scoped type-env.
  ;; exprs: the whole program, for the names bound around each body.
  ;;
  ;; In a mutual SCC, numeric descent gets no more trust than master's
  ;; per-edge rule gave it: one (- n 1) edge must not carry a cycle
  ;; through an edge that decreases nothing, since the base-case test is
  ;; not tied to the descending parameter (HC-2 round 12, C1). So the SCC
  ;; passes on structural descent alone, or when every call has a strict
  ;; arc.
  (define (scc-size-change scc-names formals-of body-of type-env-of exprs)
    (define (calls-of caller)
      (collect-intra-scc-calls
        (body-of caller) scc-names
        (append (formal-names (or (formals-of caller) '()))
                (names-bound-around exprs (body-of caller)))))
    (let ((bounded (if (and (= (length scc-names) 1) (formals-of (car scc-names)))
                       (let* ((n (car scc-names))
                              (formals (proper-formals (formals-of n))))
                         (bounded-formals
                           (upper-bound-base-cases (body-of n) n formals)
                           formals (calls-of n) (set!-targets exprs)))
                       '())))
      (define (graphs numeric-strict?)
        (apply append
          (map (lambda (caller)
                 (let ((caller-formals
                         (unassigned-formals (proper-formals (or (formals-of caller) '()))
                                             (body-of caller))))
                   (map (lambda (call)
                          (call-sc-graph caller caller-formals (type-env-of caller)
                                         bounded call
                                         (proper-formals (or (formals-of (car call)) '()))
                                         numeric-strict?))
                        (calls-of caller))))
               scc-names)))
      (sc-check-members graphs (length scc-names))))

  ;; Size-change check of one SCC. graphs-of maps numeric-strict? to the
  ;; SCC's call graphs. A mutual SCC passes on structural descent alone
  ;; (numeric arcs demoted) unless every call has a strict arc (HC-2
  ;; round 12 C1). Shared by definition SCCs and anonymous cycles
  ;; (round 13 I1).
  (define (sc-check-members graphs-of member-count)
    (let* ((gs (graphs-of #t))
           (full (sc-check gs size-change-cap)))
      (cond
        ((or (not (eq? full 'terminates)) (= member-count 1)) full)
        ((for-all (lambda (g) (exists caddr (sc-graph-arcs g))) gs) 'terminates)
        (else (sc-check (graphs-of #f) size-change-cap)))))

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
             ;; Recurse into the binding inits and the letrec body
             (for-each (lambda (binding)
                         (when (and (pair? binding) (pair? (cdr binding)))
                           (search (cadr binding))))
                       (cadr expr))
             (search-all (cddr expr)))
            ;; Operator position included: extract-definitions finds
            ;; ((letrec ((lp ...)) lp) 1) there (HC-2 round 10, I5).
            (else (search-all expr)))))
      (define (search-all lst)
        (when (pair? lst)
          (when (pair? (car lst)) (search (car lst)))
          (search-all (cdr lst))))
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
             ;; Recurse into the binding inits and the letrec body
             (for-each (lambda (binding)
                         (when (and (pair? binding) (pair? (cdr binding)))
                           (search (cadr binding))))
                       (cadr expr))
             (search-all (cddr expr)))
            ;; Operator position included: extract-definitions finds
            ;; ((letrec ((lp ...)) lp) 1) there (HC-2 round 10, I5).
            (else (search-all expr)))))
      (define (search-all lst)
        (when (pair? lst)
          (when (pair? (car lst)) (search (car lst)))
          (search-all (cdr lst))))
      (for-each search exprs)
      result))

  ;; Analyze directly recursive functions for termination.
  ;; Uses call graph + SCC to identify direct recursion (single-node SCCs
  ;; with a self-edge), then judges their calls with scc-size-change and
  ;; reuses has-base-case? from named-let analysis.
  ;; type-env: global type-env (defaults to '()).
  ;; param-types: per-function parameter type alist (defaults to '()).
  ;;   For each function, a local-type-env is built by prepending the
  ;;   function's parameter bindings to the global type-env.
  (define analyze-direct-recursion
    (case-lambda
      ((exprs) (analyze-direct-recursion exprs '() '()))
      ((exprs type-env) (analyze-direct-recursion exprs type-env '()))
      ((exprs type-env param-types)
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
                      (def-form (find-definition-form exprs name))
                      ;; Build per-function scoped type-env
                      (fn-params (assq name param-types))
                      (local-type-env (if fn-params
                                         (append (cdr fn-params) type-env)
                                         type-env)))
                 ;; Formals that cannot be extracted (case-lambda, rest
                 ;; arguments) prove no descent, so they fail closed.
                 (begin
                   (let ((progress
                           (if (or (not formals) (null? formals))
                               'no-descent
                               (scc-size-change scc
                                 (lambda (n) (find-formals-for exprs n))
                                 (lambda (n) body)
                                 (lambda (n) local-type-env)
                                 exprs))))
                     (cond
                       ((eq? progress 'limit)
                        (add-violation! 'size-change-limit name
                          (or def-form (list 'define name '...))
                          (string-append "recursive function \""
                            (symbol->string name)
                            "\" exceeds the size-change analysis limit")))

                       ;; No formals, or some cycle of recursive calls with
                       ;; no argument that shrinks all the way round
                       ((eq? progress 'no-descent)
                        (add-violation! 'no-decreasing-arg name
                          (or def-form (list 'define name '...))
                          (string-append "recursive function \""
                            (symbol->string name)
                            "\" has no decreasing argument in recursive call(s)")))

                       ;; Has valid progression but no base case at all
                       ((not (has-base-case? body name formals local-type-env))
                        (add-violation! 'no-base-case name
                          (or def-form (list 'define name '...))
                          (string-append "recursive function \""
                            (symbol->string name)
                            "\" has no reachable base case")))))))))
           sccs)

         (reverse violations)))))

  ;; ---------------------------------------------------------------
  ;; Phase 6: Mutual recursion analysis
  ;; ---------------------------------------------------------------

  ;; Binder helpers shared by collect-intra-scc-calls and the
  ;; anonymous-cycle check.
  (define (formal-names f)
    (cond
      ((symbol? f) (list f))
      ((pair? f) (append (formal-names (car f)) (formal-names (cdr f))))
      (else '())))
  (define (binding-names bs)
    (if (list? bs)
        (apply append
               (map (lambda (b) (if (pair? b) (formal-names (car b)) '())) bs))
        '()))
  (define (flatten-begins es)
    (apply append
           (map (lambda (e)
                  (if (and (pair? e) (eq? (car e) 'begin) (list? e))
                      (flatten-begins (cdr e))
                      (list e)))
                es)))
  (define (define-names es)
    (apply append
           (map (lambda (e)
                  (if (and (pair? e) (eq? (car e) 'define) (pair? (cdr e)))
                      (formal-names (cadr e))
                      '()))
                (flatten-begins es))))
  ;; Names a form binds anywhere inside itself, or '().
  (define (form-binds expr)
    (let ((tail (if (list? (cdr expr)) (cdr expr) '())))
      (append
        (case (car expr)
          ((lambda define) (if (pair? tail) (formal-names (car tail)) '()))
          ((case-lambda)
           (apply append
                  (map (lambda (c) (if (pair? c) (formal-names (car c)) '()))
                       tail)))
          ((let)
           (cond
             ((and (pair? tail) (symbol? (car tail)) (pair? (cdr tail)))
              (cons (car tail) (binding-names (cadr tail))))
             ((pair? tail) (binding-names (car tail)))
             (else '())))
          ((let* letrec letrec* let-values let*-values do)
           (if (pair? tail) (binding-names (car tail)) '()))
          (else '()))
        (define-names tail))))

  ;; Names some form in body-exprs binds around target, found by eq?,
  ;; plus the body's own defines. #f when target is not in body-exprs.
  (define (names-shadowed-at body-exprs target)
    (call/cc
      (lambda (k)
        (define (walk expr shadowed)
          (when (eq? expr target) (k shadowed))
          (when (and (pair? expr) (list? expr) (not (eq? (car expr) 'quote)))
            (let ((shadowed (if (symbol? (car expr))
                                (append (form-binds expr) shadowed)
                                shadowed)))
              (for-each (lambda (sub) (when (pair? sub) (walk sub shadowed)))
                        expr))))
        (let ((top (define-names body-exprs)))
          (for-each (lambda (e) (walk e top)) body-exprs))
        #f)))

  ;; Names bound around a definition's body: top-level defines, enclosing
  ;; binders and sibling internal defines. When the body cannot be found
  ;; in exprs, every name the program binds anywhere.
  (define (names-bound-around exprs body)
    (let* ((target (find pair? body))
           (found (and target (names-shadowed-at exprs target))))
      (or found
          (let collect ((es exprs) (acc (define-names exprs)))
            (fold-left
              (lambda (acc e)
                (if (and (pair? e) (list? e) (not (eq? (car e) 'quote)))
                    (collect e (if (symbol? (car e)) (append (form-binds e) acc) acc))
                    acc))
              acc es)))))

  ;; Collect intra-SCC call expressions from body expressions.
  ;; Returns a list of (callee-name arg-exprs...) for calls to SCC members.
  ;; Includes self-calls (since self-edges within a multi-node SCC must also
  ;; be verified as decreasing).
  ;; Calls to SCC members in body-exprs. An argument that mentions a name
  ;; some enclosing local binder rebinds is replaced by #f, which
  ;; decreases nothing: under (let ((x (list x))) ...), (car x) is not
  ;; smaller than the formal x. Binder scopes are over-approximated to
  ;; the whole form, which can only hide descent, never invent it.
  ;; user-names are names the program binds outside body-exprs, such as
  ;; top-level defines and the caller's formals: a built-in HOF's name
  ;; bound there is not that HOF.
  (define (collect-intra-scc-calls body-exprs scc-members user-names)
    (let ((calls '()))
      ;; Inside a closure that may run in a later activation, every
      ;; argument is #f: (cdr x) there is smaller than the x of the
      ;; activation that built the closure, not of the one running it.
      (define (opaque-args expr shadowed captured?)
        (cons (car expr)
              (map (lambda (a)
                     (if (or captured? (expr-references-any? a shadowed)) #f a))
                   (cdr expr))))
      (define (lambda-form? e)
        (and (pair? e) (memq (car e) '(lambda case-lambda)) #t))
      ;; Indices of the arguments a built-in calls during this very call:
      ;; a HOF's callback, dynamic-wind's three thunks, call-with-values's
      ;; producer and consumer. A shadowed built-in name may be anything.
      (define (callback-indices expr shadowed)
        (if (and (symbol? (car expr))
                 (not (memq (car expr) shadowed))
                 (not (memq (car expr) user-names)))
            (case (car expr)
              ((dynamic-wind) '(0 1 2))
              ((call-with-values) '(0 1))
              (else (let ((pos (cfa-hof-callback-position (car expr))))
                      (if pos (list pos) '()))))
            '()))
      ;; An expression whose value may outlive this activation: a lambda
      ;; there is captured.
      (define (walk-value e shadowed captured?)
        (when (pair? e)
          (walk e shadowed (or captured? (lambda-form? e)))))
      (define (walk-values es shadowed captured?)
        (for-each (lambda (e) (walk-value e shadowed captured?)) es))
      ;; True when every use of name in exprs is the operator of a call
      ;; outside any lambda, define, named let, cond, case or do, and nothing there
      ;; rebinds name. Its lambda then runs only in this activation.
      (define (called-in-place-only? name exprs)
        (define (ok? e)
          (cond
            ((symbol? e) (not (eq? e name)))
            ((not (pair? e)) #t)
            ((eq? (car e) 'quote) #t)
            ((not (list? e)) (not (expr-references-any? e (list name))))
            ((and (symbol? (car e))
                  (or (memq (car e) '(lambda case-lambda define cond case do))
                      (and (eq? (car e) 'let) (pair? (cdr e)) (symbol? (cadr e)))
                      (memq name (form-binds e))))
             (not (expr-references-any? e (list name))))
            ((eq? (car e) name) (for-all ok? (cdr e)))
            (else (for-all ok? e))))
        (for-all ok? exprs))
      ;; (let ((g (lambda ...)) ...) body ...) and let*: a binding's
      ;; lambda runs here when g is only called in place in its scope.
      (define (walk-let-bindings bindings scope-of shadowed captured?)
        (let loop ((bs bindings))
          (unless (null? bs)
            (let ((b (car bs)))
              (when (and (list? b) (= (length b) 2))
                (let ((init (cadr b)))
                  (if (and (symbol? (car b))
                           (lambda-form? init)
                           (called-in-place-only? (car b) (scope-of (cdr bs))))
                      (walk init shadowed captured?)
                      (walk-value init shadowed captured?)))))
            (loop (cdr bs)))))
      (define (walk expr shadowed captured?)
        (when (and (pair? expr) (list? expr))
          (unless (eq? (car expr) 'quote)
            (let* ((shadowed (if (symbol? (car expr))
                                 (append (form-binds expr) shadowed)
                                 shadowed))
                   (keyword (and (symbol? (car expr))
                                 (not (memq (car expr) shadowed))
                                 (not (memq (car expr) user-names))
                                 (car expr)))
                   (cbs (callback-indices expr shadowed)))
              ;; If car is an SCC member name, record the full call
              (when (and (symbol? (car expr))
                         (memq (car expr) scc-members))
                (set! calls (cons (opaque-args expr shadowed captured?) calls)))
              (cond
                ;; Clauses are not applications: every element of one is
                ;; an expression, so the call exemptions below never apply.
                ((eq? keyword 'cond)
                 (for-each (lambda (c) (when (list? c) (walk-values c shadowed captured?)))
                           (cdr expr)))
                ((and (eq? keyword 'case) (pair? (cdr expr)))
                 (walk-value (cadr expr) shadowed captured?)
                 (for-each (lambda (c)
                             (when (and (list? c) (pair? c))
                               (walk-values (cdr c) shadowed captured?)))
                           (cddr expr)))
                ((and (eq? keyword 'do) (pair? (cdr expr)) (pair? (cddr expr)))
                 (when (list? (cadr expr))
                   (for-each (lambda (spec)
                               (when (list? spec)
                                 (walk-values (if (pair? spec) (cdr spec) '())
                                              shadowed captured?)))
                             (cadr expr)))
                 (when (list? (caddr expr))
                   (walk-values (caddr expr) shadowed captured?))
                 (walk-values (cdddr expr) shadowed captured?))
                ((and (memq keyword '(let let*))
                      (pair? (cdr expr))
                      (list? (cadr expr)))
                 (let ((body (cddr expr)))
                   (walk-let-bindings
                     (cadr expr)
                     (if (eq? keyword 'let)
                         (lambda (later) body)
                         (lambda (later)
                           (append (map (lambda (b) (if (and (list? b) (pair? b) (pair? (cdr b)))
                                                        (cadr b)
                                                        b))
                                        later)
                                   body)))
                     shadowed captured?)
                   (walk-values body shadowed captured?)))
                (else
                 ;; A lambda runs in this activation only when applied on
                 ;; the spot or handed to a built-in HOF's callback slot.
                 (let loop ((subs expr) (i -1))
                   (unless (null? subs)
                     (let ((sub (car subs)))
                       (when (pair? sub)
                         (walk sub shadowed
                               (or captured?
                                   (and (lambda-form? sub)
                                        (not (= i -1))
                                        (not (memv i cbs)))))))
                     (loop (cdr subs) (+ i 1))))))))))
      (let ((top (define-names body-exprs)))
        (for-each (lambda (e) (walk e top #f)) body-exprs))
      calls))

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

  ;; Check that every cycle in the SCC passes through a member with its
  ;; own base case -- a conditional branch that does not call ANY SCC
  ;; member. One member's base case says nothing about a cycle that
  ;; avoids it, which 0CFA edges make common (HC-2 round 11, C3).
  ;; Like has-base-case?, the test must be a base-case test on a formal:
  ;; with size-change descent there is no per-edge rule left to mask a
  ;; guard that never stops a numeric descent (HC-2 round 10, I6).
  ;; graph: the call graph the SCC came from.
  (define (scc-has-base-case? exprs scc-members graph)
    (let ((found #f)
          (vars (fold-left (lambda (acc m)
                             (let ((formals (find-formals-for exprs m)))
                               (if formals (append formals acc) acc)))
                           '() scc-members)))
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
                                (or (and (base-case-test? test vars)
                                         (not (contains-scc-call? consequent)))
                                    (and alternative
                                         (negated-base-case-test? test vars '())
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
                         (when (and (or (eq? (car clause) 'else)
                                        (base-case-test? (car clause) vars))
                                    (not (contains-scc-call? body)))
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

      ;; The members without a base case of their own must not form a cycle.
      (let* ((defs (extract-definitions exprs))
             (unbased
               (filter (lambda (member)
                         (let ((entry (assq member defs)))
                           (set! found #f)
                           (when entry (check-body (cdr entry)))
                           (not found)))
                       scc-members)))
        (acyclic? unbased
                  (lambda (m)
                    (filter (lambda (c) (memq c unbased))
                            (call-graph-edges graph m)))))))

  ;; Does the graph over nodes, with successors (succ node), have no cycle?
  ;; Nodes are compared with eqv?.
  (define (acyclic? nodes succ)
    (let ((state '()))
      (define (visit n)
        (let ((st (assv n state)))
          (cond
            ((and st (eq? (cdr st) 'active)) #f)
            (st #t)
            (else
             (set! state (cons (cons n 'active) state))
             (let ((ok (for-all visit (succ n))))
               (set! state (cons (cons n 'done) state))
               ok)))))
      (for-all visit nodes)))

  ;; Analyze mutually recursive function groups for termination.
  ;; For each multi-node SCC in the call graph:
  ;;   - Check that every intra-SCC call edge passes a strictly decreasing argument
  ;;   - Check that at least one function in the SCC has a base case
  ;; If any call edge cannot be proven decreasing, flag all functions in the SCC.
  ;; type-env: global type-env (defaults to '()).
  ;; param-types: per-function parameter type alist (defaults to '()).
  (define analyze-mutual-recursion
    (case-lambda
      ((exprs) (analyze-mutual-recursion exprs '() '()))
      ((exprs type-env) (analyze-mutual-recursion exprs type-env '()))
      ((exprs type-env param-types)
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
                      (type-env-of
                        (lambda (name)
                          (let ((fn-params (assq name param-types)))
                            (if fn-params
                                (append (cdr fn-params) type-env)
                                type-env))))
                      (body-of
                        (lambda (name)
                          (let ((body-entry (assq name defs)))
                            (if body-entry (cdr body-entry) '()))))
                      (formals-of (lambda (name) (find-formals-for exprs name)))
                      ;; A member without formals cannot be checked: fail closed.
                      (progress
                        (if (exists (lambda (name)
                                      (let ((f (formals-of name)))
                                        (or (not f) (null? f))))
                                    scc-names)
                            'no-descent
                            (scc-size-change scc-names formals-of body-of type-env-of
                                             exprs)))
                      (all-edges-decrease (eq? progress 'terminates)))

                 (cond
                   ((eq? progress 'limit)
                    (for-each
                      (lambda (name)
                        (add-violation! 'size-change-limit name
                          (or (find-definition-form exprs name)
                              (list 'define name '...))
                          "mutual recursion group exceeds the size-change analysis limit"))
                      scc-names))

                   ;; Some cycle with no argument that shrinks all the way round
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
                   ((not (scc-has-base-case? exprs scc-names graph))
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
  ;; Phase 7: HOF callback termination analysis
  ;; ---------------------------------------------------------------

  ;; Check that callback functions passed to HOFs (both built-in and
  ;; user-defined) are proven terminating. Only checks symbol references
  ;; to user-defined functions. A callback symbol NOT in the user-defined
  ;; set is assumed safe — it's either a built-in or will be caught by
  ;; the separate function whitelist.
  ;; defs: alist of (name . body-exprs) from extract-definitions.
  ;; defined-names: list of all user-defined function names.
  ;; proven-terminating: list of user-defined names proven to terminate.
  ;; user-hof-table: alist of ((hof-name . callback-position) ...) from
  ;;   detect-user-defined-hofs. For user-defined HOFs, callbacks are only
  ;;   checked when the HOF itself is proven terminating — if the HOF is
  ;;   non-terminating, it is already flagged separately.
  (define check-hof-callbacks
    (case-lambda
      ((defs defined-names proven-terminating)
       (check-hof-callbacks defs defined-names proven-terminating '()))
      ((defs defined-names proven-terminating user-hof-table)
       (let ((violations '()))
         (for-each
           (lambda (def)
             (let* ((fname (car def))
                    (body (cdr def))
                    (builtin-edges (collect-hof-callback-edges body fname))
                    (user-edges (collect-user-hof-callback-edges body fname user-hof-table)))
               ;; Check built-in HOF callbacks
               (for-each
                 (lambda (edge)
                   (let ((cb-sym (cdr edge)))
                     (when (memq cb-sym defined-names)
                       (unless (memq cb-sym proven-terminating)
                         (set! violations
                           (cons (make-termination-violation
                                   'hof-callback-not-terminating
                                   fname
                                   (find-definition-form
                                     (map (lambda (d) (list 'define (car d) '...)) defs)
                                     fname)
                                   (string-append
                                     "HOF callback \"" (symbol->string cb-sym)
                                     "\" passed in function \"" (symbol->string fname)
                                     "\" is not proven terminating"))
                                 violations))))))
                 builtin-edges)
               ;; Check user-defined HOF callbacks — only when the HOF
               ;; itself is proven terminating (otherwise it is already flagged)
               (for-each
                 (lambda (edge)
                   (let ((hof-name (cadr edge))
                         (cb-sym (caddr edge)))
                     (when (memq hof-name proven-terminating)
                       (when (memq cb-sym defined-names)
                         (unless (memq cb-sym proven-terminating)
                           (set! violations
                             (cons (make-termination-violation
                                     'hof-callback-not-terminating
                                     fname
                                     (find-definition-form
                                       (map (lambda (d) (list 'define (car d) '...)) defs)
                                       fname)
                                     (string-append
                                       "HOF callback \"" (symbol->string cb-sym)
                                       "\" passed to user-defined HOF \""
                                       (symbol->string hof-name)
                                       "\" in function \"" (symbol->string fname)
                                       "\" is not proven terminating"))
                                   violations)))))))
                 user-edges)))
           defs)
         (reverse violations)))))

  ;; ---------------------------------------------------------------
  ;; Binding identity (HC-2 round 5, C4)
  ;; ---------------------------------------------------------------

  ;; The definition graph, find-formals-for and the type tables key on
  ;; the bare symbol, so a local helper named like a top-level one was
  ;; judged by the top-level one's descent. This pass gives each such
  ;; local definition its own name before any phase runs. A name is
  ;; renamed when more than one define, letrec or letrec* binder in the
  ;; program uses it, or when it looks like a synthesized lambda@N node
  ;; name. Top-level defines keep their names unless they look like
  ;; lambda@N, are named %cfa-element, or shadow a Chez builtin: the
  ;; descent predicates and 0CFA match operators such as car, - and map
  ;; by symbol, so a user's car must not be read as the builtin
  ;; (HC-2 round 7, C1/C2). Renaming is scope-correct, so renaming more than needed
  ;; changes nothing: every reference moves with its binder, a rebinding
  ;; stops it, and quoted data, case datums and quasiquoted templates
  ;; outside unquote are left alone. A violation in a renamed local
  ;; helper names it as name~N.
  (define (alpha-rename-definitions exprs)
    (let ((all-syms (make-eq-hashtable))
          (binder-count (make-eq-hashtable))
          (counter 0))

      ;; Quoted data can be cyclic, so pairs and vectors are visited once.
      (define seen (make-eq-hashtable))
      (define (note-syms! e)
        (cond
          ((symbol? e) (hashtable-set! all-syms e #t))
          ((hashtable-contains? seen e) #f)
          ((pair? e) (hashtable-set! seen e #t)
                     (note-syms! (car e)) (note-syms! (cdr e)))
          ((vector? e) (hashtable-set! seen e #t)
                       (vector-for-each note-syms! e))))

      (define (count! name)
        (when (symbol? name)
          (hashtable-update! binder-count name (lambda (n) (+ n 1)) 0)))

      ;; Over-counting only renames more, which is safe.
      (define (count-binders! e)
        (when (and (pair? e) (list? e) (not (eq? (car e) 'quote)))
          (cond
            ((and (eq? (car e) 'define) (pair? (cdr e)))
             (count! (if (pair? (cadr e)) (car (cadr e)) (cadr e))))
            ((and (memq (car e) '(letrec letrec*)) (pair? (cdr e)) (list? (cadr e)))
             (for-each (lambda (b) (when (pair? b) (count! (car b)))) (cadr e))))
          (for-each count-binders! e)))

      (define (node-name-like? name)
        (let ((str (symbol->string name)))
          (and (>= (string-length str) 7)
               (string=? (substring str 0 7) "lambda@"))))

      ;; A name the analysis reads by symbol as a builtin, a syntactic
      ;; keyword or the 0CFA element marker. A local quote would otherwise
      ;; hide a call as a datum (HC-2 round 9, C1).
      (define (misread-name? name)
        (and (symbol? name)
             (or (eq? name cfa-element-marker)
                 (eq? name cfa-spread-marker)
                 (top-level-bound? name (scheme-environment))
                 (top-level-syntax? name (scheme-environment)))))

      (define (rename? name)
        (and (symbol? name)
             (or (> (hashtable-ref binder-count name 0) 1)
                 (node-name-like? name)
                 (misread-name? name))))

      (define (fresh name)
        (set! counter (+ counter 1))
        (let ((cand (string->symbol
                      (string-append (symbol->string name) "~"
                                     (number->string counter)))))
          (if (hashtable-ref all-syms cand #f)
              (fresh name)
              (begin (hashtable-set! all-syms cand #t) cand))))

      (define (unbind env names)
        (filter (lambda (p) (not (memq (car p) names))) env))

      ;; names are bound here; those in rename? get fresh symbols.
      (define (bind env names)
        (fold-left (lambda (env name)
                     (if (rename? name)
                         (cons (cons name (fresh name)) env)
                         env))
                   (unbind env names)
                   names))

      ;; Formals, let, let-values, do and named-let variables: only a
      ;; misread name gets a fresh symbol, so an enclosing (let ((car ...)))
      ;; cannot pass for the builtin car (HC-2 round 8, C1).
      (define (bind-local env names)
        (fold-left (lambda (env name)
                     (if (misread-name? name)
                         (cons (cons name (fresh name)) env)
                         env))
                   (unbind env names)
                   names))

      (define (ref env e)
        (let ((p (assq e env))) (if p (cdr p) e)))

      ;; Rewrite a binder: a symbol, a formals list or an improper one.
      (define (rn-formals fs env)
        (cond
          ((symbol? fs) (ref env fs))
          ((pair? fs) (cons (rn-formals (car fs) env) (rn-formals (cdr fs) env)))
          (else fs)))

      ;; let-style bindings: each variable takes its name in inner.
      (define (rn-binding-vars bs inner)
        (if (list? bs)
            (map (lambda (b) (if (pair? b) (cons (rn-formals (car b) inner) (cdr b)) b)) bs)
            bs))

      (define (body-define-names forms)
        (apply append
               (map (lambda (f)
                      (cond
                        ((and (pair? f) (eq? (car f) 'define) (pair? (cdr f)))
                         (let ((t (cadr f)))
                           (if (pair? t)
                               (if (symbol? (car t)) (list (car t)) '())
                               (if (symbol? t) (list t) '()))))
                        ((and (pair? f) (eq? (car f) 'begin) (list? f))
                         (body-define-names (cdr f)))
                        (else '())))
                    forms)))

      ;; A body: its defines bind across the whole body.
      (define (rn-body forms env)
        (if (list? forms)
            (let ((env (bind env (body-define-names forms))))
              (map (lambda (f) (rn-body-form f env)) forms))
            (rn forms env)))

      (define (rn-body-form f env)
        (cond
          ((and (pair? f) (eq? (car f) 'define) (pair? (cdr f)) (list? f))
           (let ((t (cadr f)))
             (if (pair? t)
                 (let ((inner (bind-local env (formal-names (cdr t)))))
                   (cons* 'define
                          (cons (ref env (car t)) (rn-formals (cdr t) inner))
                          (rn-body (cddr f) inner)))
                 (cons* 'define (ref env t) (map (lambda (x) (rn x env)) (cddr f))))))
          ((and (pair? f) (eq? (car f) 'begin) (list? f))
           (cons 'begin (map (lambda (x) (rn-body-form x env)) (cdr f))))
          (else (rn f env))))

      (define (rn-bindings bs env)
        (if (list? bs)
            (map (lambda (b)
                   (if (and (pair? b) (list? b))
                       (cons (car b) (map (lambda (x) (rn x env)) (cdr b)))
                       b))
                 bs)
            bs))

      (define (rn-qq x env depth)
        (cond
          ((not (pair? x)) x)
          ((and (memq (car x) '(unquote unquote-splicing)) (pair? (cdr x)) (null? (cddr x)))
           (if (= depth 1)
               (list (car x) (rn (cadr x) env))
               (list (car x) (rn-qq (cadr x) env (- depth 1)))))
          ((and (eq? (car x) 'quasiquote) (pair? (cdr x)) (null? (cddr x)))
           (list 'quasiquote (rn-qq (cadr x) env (+ depth 1))))
          (else (cons (rn-qq (car x) env depth) (rn-qq (cdr x) env depth)))))

      (define (rn-generic e env)
        (cond
          ((pair? e) (cons (rn (car e) env) (rn-generic (cdr e) env)))
          ((null? e) e)
          (else (rn e env))))

      (define (rn e env)
        (cond
          ((symbol? e) (ref env e))
          ((not (pair? e)) e)
          ((or (not (list? e)) (not (symbol? (car e))) (assq (car e) env))
           (rn-generic e env))
          (else
           (let ((tail (cdr e)))
             (case (car e)
               ((quote) e)
               ((quasiquote)
                (if (and (pair? tail) (null? (cdr tail)))
                    (list 'quasiquote (rn-qq (car tail) env 1))
                    e))
               ((lambda)
                (if (pair? tail)
                    (let ((inner (bind-local env (formal-names (car tail)))))
                      (cons* 'lambda (rn-formals (car tail) inner)
                             (rn-body (cdr tail) inner)))
                    e))
               ((case-lambda)
                (cons 'case-lambda
                      (map (lambda (c)
                             (if (pair? c)
                                 (let ((inner (bind-local env (formal-names (car c)))))
                                   (cons (rn-formals (car c) inner) (rn-body (cdr c) inner)))
                                 c))
                           tail)))
               ((define) (rn-body-form e env))
               ((let)
                (cond
                  ((and (pair? tail) (symbol? (car tail)) (pair? (cdr tail)))
                   (let ((inner (bind-local env (cons (car tail) (binding-names (cadr tail))))))
                     (cons* 'let (ref inner (car tail))
                            (rn-binding-vars (rn-bindings (cadr tail) env) inner)
                            (rn-body (cddr tail) inner))))
                  ((pair? tail)
                   (let ((inner (bind-local env (binding-names (car tail)))))
                     (cons* 'let (rn-binding-vars (rn-bindings (car tail) env) inner)
                            (rn-body (cdr tail) inner))))
                  (else e)))
               ((let* let*-values)
                (if (and (pair? tail) (list? (car tail)))
                    (let loop ((bs (car tail)) (env env) (acc '()))
                      (if (null? bs)
                          (cons* (car e) (reverse acc) (rn-body (cdr tail) env))
                          (let* ((b (car bs))
                                 (inner (if (pair? b) (bind-local env (formal-names (car b))) env)))
                            (loop (cdr bs)
                                  inner
                                  (cons (car (rn-binding-vars (rn-bindings (list b) env) inner))
                                        acc)))))
                    e))
               ((let-values)
                (if (pair? tail)
                    (let ((inner (bind-local env (binding-names (car tail)))))
                      (cons* 'let-values (rn-binding-vars (rn-bindings (car tail) env) inner)
                             (rn-body (cdr tail) inner)))
                    e))
               ((letrec letrec*)
                (if (pair? tail)
                    (let ((env (bind env (binding-names (car tail)))))
                      (cons* (car e)
                             (if (list? (car tail))
                                 (map (lambda (b)
                                        (if (and (pair? b) (list? b))
                                            (cons (ref env (car b))
                                                  (map (lambda (x) (rn x env)) (cdr b)))
                                            b))
                                      (car tail))
                                 (car tail))
                             (rn-body (cdr tail) env)))
                    e))
               ((do)
                (if (and (pair? tail) (list? (car tail)) (pair? (cdr tail)))
                    (let ((inner (bind-local env (binding-names (car tail)))))
                      (cons* 'do
                             (map (lambda (b)
                                    (if (and (pair? b) (list? b) (pair? (cdr b)))
                                        (cons* (ref inner (car b)) (rn (cadr b) env)
                                               (map (lambda (x) (rn x inner)) (cddr b)))
                                        b))
                                  (car tail))
                             (rn (cadr tail) inner)
                             (map (lambda (x) (rn x inner)) (cddr tail))))
                    e))
               ((case)
                (if (pair? tail)
                    (cons* 'case (rn (car tail) env)
                           (map (lambda (c)
                                  (if (and (pair? c) (list? c))
                                      (cons (car c) (map (lambda (x) (rn x env)) (cdr c)))
                                      c))
                                (cdr tail)))
                    e))
               ((guard)
                (if (and (pair? tail) (pair? (car tail)) (list? (car tail)))
                    (let* ((var (caar tail))
                           (inner (bind-local env (list var))))
                      (cons* 'guard
                             (cons (ref inner var) (map (lambda (c) (rn c inner))
                                                        (cdar tail)))
                             (rn-body (cdr tail) env)))
                    e))
               (else (rn-generic e env)))))))

      (note-syms! exprs)
      (for-each count-binders! exprs)
      ;; Top level: only names the analysis would misread are renamed.
      (let ((top-env
              (fold-left (lambda (env name)
                           (if (and (symbol? name)
                                    (or (node-name-like? name)
                                        (misread-name? name))
                                    (not (assq name env)))
                               (cons (cons name (fresh name)) env)
                               env))
                         '()
                         (body-define-names exprs))))
        (values (map (lambda (f) (rn-body-form f top-env)) exprs)
                top-env))))

  ;; A renamed top-level definition is reported under its own name. Top
  ;; level names are unique once duplicates are rejected, so top-env,
  ;; an alist of (name . fresh), inverts. In the reason text a fresh
  ;; name only matches when no digit follows, so car~1 leaves car~12.
  (define (restore-top-level-names v top-env)
    (define (old-name sym)
      (let ((p (find (lambda (q) (eq? (cdr q) sym)) top-env)))
        (if p (car p) sym)))
    (define (restore-expr e)
      (cond
        ((symbol? e) (old-name e))
        ((pair? e) (cons (restore-expr (car e)) (restore-expr (cdr e))))
        (else e)))
    (define (replace-name str from to)
      (let ((n (string-length str)) (k (string-length from)))
        (let loop ((i 0) (acc '()))
          (cond
            ((> (+ i k) n)
             (apply string-append (reverse (cons (substring str i n) acc))))
            ((and (string=? (substring str i (+ i k)) from)
                  (or (= (+ i k) n)
                      (not (char-numeric? (string-ref str (+ i k))))))
             (loop (+ i k) (cons to acc)))
            (else
             (loop (+ i 1) (cons (string (string-ref str i)) acc)))))))
    (if (null? top-env)
        v
        (make-termination-violation
          (termination-violation-kind v)
          (let ((f (termination-violation-function v)))
            (if (symbol? f) (old-name f) f))
          (restore-expr (termination-violation-expr v))
          (let ((r (termination-violation-reason v)))
            (if (string? r)
                (fold-left (lambda (r q)
                             (replace-name r (symbol->string (cdr q))
                                           (symbol->string (car q))))
                           r top-env)
                r)))))

  ;; ---------------------------------------------------------------
  ;; Main entry point
  ;; ---------------------------------------------------------------

  ;; check-termination : (list-of expr) x type-env [x param-types [x max-definitions]] -> (list-of termination-violation)
  ;; Analyzes expressions for potential non-termination.
  ;; type-env: global type-env alist (function-level signatures).
  ;; param-types: per-function parameter type alist ((fn-name . ((param . type) ...)) ...)
  ;;   from build-type-env.  Each function's bindings are prepended to type-env
  ;;   when analyzing that function's body (syntactic scoping).
  ;; Optional max-definitions parameter: when set, block the program if it has
  ;; more definitions than this limit (emit a definition-limit-exceeded violation).
  ;; A value of 0 blocks all programs with any definitions. #f means no limit (default).
  (define check-termination
    (case-lambda
      ((exprs type-env)
       (check-termination exprs type-env '() #f))
      ((exprs type-env param-types)
       (check-termination exprs type-env param-types #f))
      ((exprs type-env param-types max-definitions)
       (if (cyclic-datum? exprs)
           (list (make-termination-violation
                   'cyclic-datum #f #f
                   "source contains a cyclic datum (#n= label); descent on car, cdr and vector-ref assumes acyclic data"))
           (let-values (((renamed top-env) (alpha-rename-definitions exprs)))
             (append (duplicate-top-level-definitions exprs)
                     (map (lambda (v) (restore-top-level-names v top-env))
                          (check-termination-renamed renamed type-env param-types
                                                     max-definitions))))))))

  ;; Every descent rule assumes data is acyclic, because set-car!,
  ;; set-cdr! and vector-set! on quoted data are not whitelisted. A
  ;; #n= label in the source is the one way to build a cycle without
  ;; them, and a cyclic code form would hang every walker below, so the
  ;; whole program is rejected before analysis (HC-2 round 14, minor).
  ;; Shared but acyclic structure, such as '(#0=(1) #0#), is accepted.
  (define (cyclic-datum? x)
    (let ((on-path (make-eq-hashtable))
          (done (make-eq-hashtable)))
      (let walk ((x x))
        (cond
          ((not (or (pair? x) (vector? x))) #f)
          ((hashtable-contains? done x) #f)
          ((hashtable-contains? on-path x) #t)
          (else
           (hashtable-set! on-path x #t)
           (let ((found (if (pair? x)
                            (or (walk (car x)) (walk (cdr x)))
                            (let loop ((i 0))
                              (and (< i (vector-length x))
                                   (or (walk (vector-ref x i))
                                       (loop (+ i 1))))))))
             (hashtable-delete! on-path x)
             (hashtable-set! done x #t)
             found))))))

  ;; A second top-level define of a name rebinds the same variable, so
  ;; every earlier body calls the later value, while the definition
  ;; graph keys on the name and judges only one of them. Fail closed:
  ;; one violation per name defined more than once (HC-2 round 6, I1).
  (define (duplicate-top-level-definitions exprs)
    (let loop ((names (filter symbol?
                        (map (lambda (e)
                             (let ((t (cadr e)))
                               (if (pair? t) (car t) t)))
                           (filter (lambda (e)
                                     (and (pair? e) (eq? (car e) 'define)
                                          (pair? (cdr e))))
                                   (flatten-begins exprs)))))
               (seen '())
               (acc '()))
      (cond
        ((null? names) (reverse acc))
        ((and (memq (car names) seen) (not (memq (car names) (map termination-violation-function acc))))
         (loop (cdr names) seen
               (cons (make-termination-violation
                       'duplicate-definition (car names) #f
                       (string-append "\"" (symbol->string (car names))
                                      "\" is defined more than once at top level"))
                     acc)))
        (else (loop (cdr names) (cons (car names) seen) acc)))))

  (define (check-termination-renamed exprs type-env param-types max-definitions)
    (let ((do-violations (analyze-do-forms exprs))
          (named-let-violations (analyze-named-let-forms exprs type-env param-types))
          (defs (extract-definitions exprs)))
      (if (and max-definitions
               (> (length defs) max-definitions))
          ;; Depth limit exceeded: block the program
          (append do-violations
                  named-let-violations
                  (list (make-termination-violation
                          'definition-limit-exceeded
                          #f
                          #f
                          (string-append "definition count "
                            (number->string (length defs))
                            " exceeds analysis limit "
                            (number->string max-definitions)))))
          ;; Full analysis including HOF callback checks
          (let* ((defined-names (map car defs))
                 ;; Phases 5 and 6 run on the program with 0CFA's
                 ;; higher-order call edges made explicit (HC-2).
                 (cfa-pair (call-with-values
                             (lambda () (cfa-analyze-program exprs))
                             cons))
                 (cfa-exprs (car cfa-pair))
                 (graph (build-call-graph cfa-exprs))
                 (sccs (tarjan-scc graph))
                 (base-violations
                   (append (analyze-direct-recursion cfa-exprs type-env param-types)
                           (analyze-mutual-recursion cfa-exprs type-env param-types)
                           (cdr cfa-pair)))
                 (violated-names
                   (map termination-violation-function base-violations))
                 ;; "Can prove terminates" model: a function is proven
                 ;; terminating only if the checker can positively confirm it.
                 ;; - Trivially non-recursive (single-node SCC, no self-edge):
                 ;;   proven by call-graph structure.
                 ;; - Recursive but analyzed without violations: proven by
                 ;;   Phase 5/6 analysis.
                 ;; This fails closed: any function the checker cannot
                 ;; positively confirm is excluded from the proven set.
                 (trivially-non-recursive
                   (let loop ((remaining sccs) (acc '()))
                     (if (null? remaining)
                         acc
                         (let ((scc (car remaining)))
                           (if (and (= (length scc) 1)
                                    (not (memq (car scc)
                                               (call-graph-edges graph (car scc)))))
                               (loop (cdr remaining) (cons (car scc) acc))
                               (loop (cdr remaining) acc))))))
                 (proven-terminating
                   (filter
                     (lambda (n)
                       (or
                         ;; Non-recursive: proven by structure
                         (memq n trivially-non-recursive)
                         ;; Recursive: proven by analysis (no violations)
                         (not (memq n violated-names))))
                     defined-names))
                 ;; Detect user-defined HOFs and check their callbacks
                 (user-hof-table (detect-user-defined-hofs defs exprs))
                 (hof-violations
                   (check-hof-callbacks defs defined-names proven-terminating
                                        user-hof-table)))
            (append do-violations
                    named-let-violations
                    base-violations
                    hof-violations)))))
)
