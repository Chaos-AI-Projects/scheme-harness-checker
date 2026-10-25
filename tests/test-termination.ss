;; test-termination.ss
;; Tests for the termination analysis pass.
;;
;; Run with: scheme --libdirs ../src --program test-termination.ss

(import (rnrs)
        (harness-checker termination)
        (harness-checker whitelist-checker)
        (harness-checker types))

(define pass-count 0)
(define fail-count 0)

(define (assert-equal test-name expected actual)
  (if (equal? expected actual)
      (begin
        (set! pass-count (+ pass-count 1))
        (display "  PASS: ") (display test-name) (newline))
      (begin
        (set! fail-count (+ fail-count 1))
        (display "  FAIL: ") (display test-name) (newline)
        (display "    expected: ") (write expected) (newline)
        (display "    actual:   ") (write actual) (newline))))

(define (assert-true test-name value)
  (assert-equal test-name #t value))

(define (assert-no-violations test-name violations)
  (if (null? violations)
      (begin
        (set! pass-count (+ pass-count 1))
        (display "  PASS: ") (display test-name) (newline))
      (begin
        (set! fail-count (+ fail-count 1))
        (display "  FAIL: ") (display test-name) (newline)
        (display "    expected no violations but got ") (display (length violations))
        (newline))))

(define (assert-violation-count test-name expected-count violations)
  (let ((actual (length violations)))
    (if (= expected-count actual)
        (begin
          (set! pass-count (+ pass-count 1))
          (display "  PASS: ") (display test-name) (newline))
        (begin
          (set! fail-count (+ fail-count 1))
          (display "  FAIL: ") (display test-name) (newline)
          (display "    expected ") (display expected-count)
          (display " violation(s), got ") (display actual) (newline)))))

;; Helper: parse source and run termination check
(define (check-source-termination source)
  (let ((exprs (read-all-expressions source)))
    (check-termination exprs '())))

;; Helper: parse source and build call graph
(define (source->call-graph source)
  (let ((exprs (read-all-expressions source)))
    (build-call-graph exprs)))

;; Helper: parse source and run Tarjan's SCC
(define (source->sccs source)
  (let* ((exprs (read-all-expressions source))
         (graph (build-call-graph exprs)))
    (tarjan-scc graph)))

;; Helper: check if a list contains a given element
(define (list-contains? lst elem)
  (and (memq elem lst) #t))

;; Helper: find the SCC containing a given node
(define (find-scc-containing sccs node)
  (let loop ((remaining sccs))
    (if (null? remaining)
        #f
        (if (memq node (car remaining))
            (car remaining)
            (loop (cdr remaining))))))

;; Helper: sort a list of symbols for deterministic comparison
(define (sort-symbols syms)
  (list-sort (lambda (a b)
               (string<? (symbol->string a) (symbol->string b)))
             syms))

;; ============================================================
;; Test Group: Record type
;; ============================================================
(display "=== Record type ===") (newline)

(assert-true "termination-violation? on constructed record"
  (termination-violation?
    (make-termination-violation 'unbounded-loop 'foo '(foo) "test reason")))

(assert-equal "kind accessor"
  'unbounded-loop
  (termination-violation-kind
    (make-termination-violation 'unbounded-loop 'foo '(foo) "test reason")))

(assert-equal "function accessor"
  'foo
  (termination-violation-function
    (make-termination-violation 'unbounded-loop 'foo '(foo) "test reason")))

(assert-equal "expr accessor"
  '(foo)
  (termination-violation-expr
    (make-termination-violation 'unbounded-loop 'foo '(foo) "test reason")))

(assert-equal "reason accessor"
  "test reason"
  (termination-violation-reason
    (make-termination-violation 'unbounded-loop 'foo '(foo) "test reason")))

;; ============================================================
;; Test Group: check-termination still returns empty (no violations yet)
;; ============================================================
(display "=== check-termination returns empty ===") (newline)

(assert-no-violations "empty input"
  (check-source-termination ""))

(assert-no-violations "simple arithmetic"
  (check-source-termination "(+ 1 2)"))

(assert-no-violations "define and call"
  (check-source-termination "(define (f x) (+ x 1)) (f 42)"))

(assert-no-violations "recursive function (terminating factorial)"
  (check-source-termination
    "(define (factorial n) (if (<= n 0) 1 (* n (factorial (- n 1)))))"))

(assert-no-violations "valid do loop"
  (check-source-termination
    "(do ((i 0 (+ i 1))) ((= i 10) i) (display i))"))

(assert-no-violations "named let loop with decreasing arg and base case"
  (check-source-termination
    "(let loop ((i 0)) (when (< i 10) (display i) (loop (+ i 1))))"))

(assert-no-violations "mutual recursion (valid even?/odd?)"
  (check-source-termination
    "(define (even? n) (if (<= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (<= n 0) #f (even? (- n 1))))"))

(assert-true "result is a list"
  (list? (check-source-termination "(define (f x) x)")))

(assert-equal "result is empty list"
  '()
  (check-source-termination "(define (f x) x)"))

;; ============================================================
;; Test Group: Definition extraction
;; ============================================================
(display "=== Definition extraction ===") (newline)

(let ((defs (extract-definitions
              (read-all-expressions "(define (f x) (+ x 1))"))))
  (assert-equal "extracts define-fn name"
    'f
    (caar defs))
  (assert-equal "extracts define-fn body"
    '((+ x 1))
    (cdar defs)))

(let ((defs (extract-definitions
              (read-all-expressions "(define f (lambda (x) (+ x 1)))"))))
  (assert-equal "extracts define-lambda name"
    'f
    (caar defs))
  (assert-equal "extracts define-lambda body"
    '((+ x 1))
    (cdar defs)))

(let ((defs (extract-definitions
              (read-all-expressions
                "(define f (case-lambda ((x) (+ x 1)) ((x y) (+ x y))))"))))
  (assert-equal "extracts case-lambda name"
    'f
    (caar defs)))

(let ((defs (extract-definitions
              (read-all-expressions "(+ 1 2)"))))
  (assert-equal "non-definition returns empty"
    '()
    defs))

(let ((defs (extract-definitions
              (read-all-expressions
                "(define (f x) (+ x 1)) (define (g y) (* y 2))"))))
  (assert-equal "extracts multiple definitions"
    2
    (length defs)))

;; ============================================================
;; Test Group: Call graph - direct recursion
;; ============================================================
(display "=== Call graph: direct recursion ===") (newline)

(let ((graph (source->call-graph
               "(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))")))
  (assert-true "fact->fact edge exists"
    (list-contains? (call-graph-edges graph 'fact) 'fact))
  (assert-equal "fact has exactly one edge (self)"
    '(fact)
    (call-graph-edges graph 'fact)))

;; ============================================================
;; Test Group: Call graph - mutual recursion
;; ============================================================
(display "=== Call graph: mutual recursion ===") (newline)

(let ((graph (source->call-graph
               (string-append
                 "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) "
                 "(define (odd? n) (if (= n 0) #f (even? (- n 1))))"))))
  (assert-true "even?->odd? edge exists"
    (list-contains? (call-graph-edges graph 'even?) 'odd?))
  (assert-true "odd?->even? edge exists"
    (list-contains? (call-graph-edges graph 'odd?) 'even?)))

;; ============================================================
;; Test Group: Call graph - non-recursive function
;; ============================================================
(display "=== Call graph: non-recursive ===") (newline)

(let ((graph (source->call-graph
               "(define (add x y) (+ x y))")))
  (assert-equal "non-recursive function has no edges"
    '()
    (call-graph-edges graph 'add)))

(let ((graph (source->call-graph
               "(define (f x) (+ x 1)) (define (g y) (* y 2))")))
  (assert-equal "f has no edges (does not call g)"
    '()
    (call-graph-edges graph 'f))
  (assert-equal "g has no edges (does not call f)"
    '()
    (call-graph-edges graph 'g)))

;; ============================================================
;; Test Group: Call graph - caller/callee (non-recursive)
;; ============================================================
(display "=== Call graph: caller/callee ===") (newline)

(let ((graph (source->call-graph
               "(define (double x) (* x 2)) (define (quad x) (double (double x)))")))
  (assert-equal "double has no edges"
    '()
    (call-graph-edges graph 'double))
  (assert-equal "quad calls double"
    '(double)
    (call-graph-edges graph 'quad)))

;; ============================================================
;; Test Group: Call graph - quoted forms ignored
;; ============================================================
(display "=== Call graph: quoted forms ===") (newline)

(let ((graph (source->call-graph
               "(define (f x) (list 'g x)) (define (g y) y)")))
  (assert-equal "quoted g is not a call edge"
    '()
    (call-graph-edges graph 'f)))

;; ============================================================
;; Test Group: Tarjan's SCC - direct recursion
;; ============================================================
(display "=== SCC: direct recursion ===") (newline)

(let* ((graph (source->call-graph
                "(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))"))
       (sccs (tarjan-scc graph))
       (fact-scc (find-scc-containing sccs 'fact)))
  (assert-true "fact is in an SCC"
    (and fact-scc #t))
  (assert-equal "fact SCC has one member"
    '(fact)
    fact-scc))

;; ============================================================
;; Test Group: Tarjan's SCC - mutual recursion
;; ============================================================
(display "=== SCC: mutual recursion ===") (newline)

(let* ((graph (source->call-graph
                (string-append
                  "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) "
                  "(define (odd? n) (if (= n 0) #f (even? (- n 1))))")))
       (sccs (tarjan-scc graph))
       (even-scc (find-scc-containing sccs 'even?))
       (odd-scc (find-scc-containing sccs 'odd?)))
  (assert-true "even? and odd? are in the same SCC"
    (eq? even-scc odd-scc))
  (assert-equal "mutual recursion SCC has two members"
    '(even? odd?)
    (sort-symbols even-scc)))

;; ============================================================
;; Test Group: Tarjan's SCC - non-recursive
;; ============================================================
(display "=== SCC: non-recursive ===") (newline)

(let* ((graph (source->call-graph
                "(define (add x y) (+ x y))"))
       (sccs (tarjan-scc graph))
       (add-scc (find-scc-containing sccs 'add)))
  (assert-true "non-recursive function is in a trivial SCC"
    (and add-scc #t))
  (assert-equal "trivial SCC has one member"
    '(add)
    add-scc))

;; ============================================================
;; Test Group: Tarjan's SCC - mixed graph
;; ============================================================
(display "=== SCC: mixed graph ===") (newline)

(let* ((graph (source->call-graph
                (string-append
                  "(define (helper x) (+ x 1)) "
                  "(define (fact n) (if (= n 0) 1 (* n (fact (- n (helper 0)))))) "
                  "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) "
                  "(define (odd? n) (if (= n 0) #f (even? (- n 1))))")))
       (sccs (tarjan-scc graph))
       (helper-scc (find-scc-containing sccs 'helper))
       (fact-scc (find-scc-containing sccs 'fact))
       (even-scc (find-scc-containing sccs 'even?)))
  (assert-equal "helper is in trivial SCC"
    '(helper)
    helper-scc)
  (assert-equal "fact is in its own SCC (self-recursive)"
    '(fact)
    fact-scc)
  (assert-equal "even?/odd? share an SCC"
    '(even? odd?)
    (sort-symbols even-scc)))

;; ============================================================
;; Test Group: Call graph - letrec definitions
;; ============================================================
(display "=== Call graph: letrec ===") (newline)

(let ((defs (extract-definitions
              (read-all-expressions
                (string-append
                  "(letrec ((ping (lambda (n) (if (= n 0) 'done (pong (- n 1))))) "
                  "         (pong (lambda (n) (if (= n 0) 'done (ping (- n 1)))))) "
                  "  (ping 10))")))))
  (assert-equal "letrec extracts two definitions"
    2
    (length defs))
  (assert-true "letrec extracts ping"
    (and (assq 'ping defs) #t))
  (assert-true "letrec extracts pong"
    (and (assq 'pong defs) #t)))

;; ============================================================
;; Test Group: Internal (nested) defines
;; ============================================================
(display "=== Internal defines ===") (newline)

(let ((defs (extract-definitions
              (read-all-expressions
                "(define (outer x) (define (inner y) (+ y 1)) (inner x))"))))
  (assert-equal "extracts both outer and inner defines"
    2
    (length defs))
  (assert-true "extracts outer"
    (and (assq 'outer defs) #t))
  (assert-true "extracts inner"
    (and (assq 'inner defs) #t)))

(let ((graph (source->call-graph
               "(define (outer x) (define (inner y) (+ y 1)) (inner x))")))
  (assert-true "outer calls inner"
    (list-contains? (call-graph-edges graph 'outer) 'inner))
  (assert-equal "inner has no edges"
    '()
    (call-graph-edges graph 'inner)))

;; ============================================================
;; Test Group: Call position vs argument position
;; ============================================================
(display "=== Call position distinction ===") (newline)

;; In (f (g x)), both f and g are in call position.
;; But in (h 'f), f is NOT in call position (it's quoted).
(let ((graph (source->call-graph
               (string-append
                 "(define (f x) (g x)) "
                 "(define (g y) y) "
                 "(define (h z) (list 'f z))"))))
  (assert-equal "f calls g"
    '(g)
    (call-graph-edges graph 'f))
  (assert-equal "g has no edges"
    '()
    (call-graph-edges graph 'g))
  (assert-equal "h does not call f (quoted)"
    '()
    (call-graph-edges graph 'h)))

;; Nested call: (f (g (h x))) should record f->g and f->h
(let ((graph (source->call-graph
               (string-append
                 "(define (f x) (g (h x))) "
                 "(define (g y) y) "
                 "(define (h z) z)"))))
  (assert-true "f calls g (in call position)"
    (list-contains? (call-graph-edges graph 'f) 'g))
  (assert-true "f calls h (nested in argument)"
    (list-contains? (call-graph-edges graph 'f) 'h)))

;; ============================================================
;; Test Group: Empty and edge cases
;; ============================================================
(display "=== Edge cases ===") (newline)

(let ((graph (source->call-graph "")))
  (assert-equal "empty source produces empty graph"
    '()
    graph))

(let ((graph (source->call-graph "(+ 1 2) (display \"hello\")")))
  (assert-equal "no definitions produces empty graph"
    '()
    graph))

(let* ((graph (source->call-graph
                "(define (f x) (if x (f (not x)) x))"))
       (sccs (tarjan-scc graph)))
  (assert-equal "single self-recursive function: one SCC"
    1
    (length sccs)))

;; ============================================================
;; Test Group: Do-form analysis - valid forms (no violations)
;; ============================================================
(display "=== Do-form analysis: valid ===") (newline)

(assert-no-violations "do with step and test passes"
  (check-source-termination
    "(do ((i 0 (+ i 1))) ((= i 10)) (display i))"))

(assert-no-violations "do with multiple bindings, one has step"
  (check-source-termination
    "(do ((i 0 (+ i 1)) (j 0)) ((= i 10)) (display i))"))

(assert-no-violations "do with all bindings having steps"
  (check-source-termination
    "(do ((i 0 (+ i 1)) (j 10 (- j 1))) ((= i 10)) (display j))"))

(assert-no-violations "do nested inside define passes when valid"
  (check-source-termination
    "(define (count-up n) (do ((i 0 (+ i 1))) ((= i n)) (display i)))"))

;; ============================================================
;; Test Group: Do-form analysis - trivially false test (#f)
;; ============================================================
(display "=== Do-form analysis: #f test ===") (newline)

(let ((violations (check-source-termination
                    "(do ((i 0 (+ i 1))) (#f) (display i))")))
  (assert-violation-count "do with #f test flags infinite-loop" 1 violations)
  (assert-equal "do #f test violation kind"
    'infinite-loop
    (termination-violation-kind (car violations)))
  (assert-equal "do violation function is #f"
    #f
    (termination-violation-function (car violations))))

;; ============================================================
;; Test Group: Do-form analysis - no step expression
;; ============================================================
(display "=== Do-form analysis: no step ===") (newline)

(let ((violations (check-source-termination
                    "(do ((i 0)) ((= i 10)) (display i))")))
  (assert-violation-count "do without step flags infinite-loop" 1 violations)
  (assert-equal "do no-step violation kind"
    'infinite-loop
    (termination-violation-kind (car violations))))

;; ============================================================
;; Test Group: Do-form analysis - test doesn't reference loop var
;; ============================================================
(display "=== Do-form analysis: test ignores loop var ===") (newline)

(let ((violations (check-source-termination
                    "(do ((i 0 (+ i 1))) ((= x 10)) (display i))")))
  (assert-violation-count "do test not referencing loop var flags" 1 violations)
  (assert-equal "do test-no-ref violation kind"
    'infinite-loop
    (termination-violation-kind (car violations))))

;; ============================================================
;; Test Group: Do-form analysis - nested do-forms
;; ============================================================
(display "=== Do-form analysis: nested ===") (newline)

(assert-no-violations "nested valid do-forms"
  (check-source-termination
    "(do ((i 0 (+ i 1))) ((= i 5)) (do ((j 0 (+ j 1))) ((= j 3)) (display j)))"))

(let ((violations (check-source-termination
                    "(do ((i 0 (+ i 1))) ((= i 5)) (do ((j 0)) ((= j 3)) (display j)))")))
  (assert-violation-count "nested do: inner invalid flagged" 1 violations))

;; ============================================================
;; Test Group: Named-let analysis - valid forms (no violations)
;; ============================================================
(display "=== Named-let analysis: valid ===") (newline)

;; Issue #273 test 1: decreasing arg + base case
(assert-no-violations "named-let with decreasing arg and base case"
  (check-source-termination
    "(let loop ((n 10)) (if (<= n 0) 0 (loop (- n 1))))"))

(assert-no-violations "named-let with sub1 decrease"
  (check-source-termination
    "(let loop ((n 10)) (if (<= n 0) 0 (loop (sub1 n))))"))

(assert-no-violations "named-let with fx- decrease"
  (check-source-termination
    "(let loop ((n 10)) (if (<= n 0) 0 (loop (fx- n 1))))"))

(assert-no-violations "named-let with cdr structural decrease"
  (check-source-termination
    "(let loop ((lst '(1 2 3))) (if (null? lst) 0 (loop (cdr lst))))"))

(assert-no-violations "named-let with cddr structural decrease"
  (check-source-termination
    "(let loop ((lst '(1 2 3 4))) (if (null? lst) 0 (loop (cddr lst))))"))

(assert-no-violations "named-let with list-tail structural decrease"
  (check-source-termination
    "(let loop ((lst '(1 2 3))) (if (null? lst) 0 (loop (list-tail lst 1))))"))

(assert-no-violations "named-let with (not (pair? x)) base case"
  (check-source-termination
    "(let loop ((lst '(1 2 3))) (if (not (pair? lst)) 0 (loop (cdr lst))))"))

(assert-no-violations "named-let with (< x 1) base case"
  (check-source-termination
    "(let loop ((n 10)) (if (< n 1) 0 (loop (- n 1))))"))

(assert-no-violations "named-let with (<= x 0) base case"
  (check-source-termination
    "(let loop ((n 10)) (if (<= n 0) 0 (loop (- n 1))))"))

(assert-no-violations "named-let with when guard (implicit base case)"
  (check-source-termination
    "(let loop ((n 10)) (when (> n 0) (display n) (loop (- n 1))))"))

(assert-no-violations "named-let with unless guard"
  (check-source-termination
    "(let loop ((n 10)) (unless (<= n 0) (display n) (loop (- n 1))))"))

(assert-no-violations "named-let with cond guard"
  (check-source-termination
    "(let loop ((n 10)) (cond ((<= n 0) 'done) (else (loop (- n 1)))))"))

(assert-no-violations "named-let with multiple args, one decreasing"
  (check-source-termination
    "(let loop ((n 10) (acc 0)) (if (<= n 0) acc (loop (- n 1) (+ acc n))))"))

(assert-no-violations "named-let nested inside define"
  (check-source-termination
    "(define (sum-to n) (let loop ((i n) (acc 0)) (if (<= i 0) acc (loop (- i 1) (+ acc i)))))"))

;; ============================================================
;; Test Group: Named-let analysis - no decreasing argument
;; ============================================================
(display "=== Named-let analysis: no decreasing arg ===") (newline)

;; Issue #273 test 2: no decreasing arg
(let ((violations (check-source-termination
                    "(let loop ((n 10)) (loop n))")))
  (assert-violation-count "named-let with no decreasing arg" 1 violations)
  (assert-equal "named-let no-decrease kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations)))
  (assert-equal "named-let no-decrease function is loop name"
    'loop
    (termination-violation-function (car violations))))

(let ((violations (check-source-termination
                    "(let loop ((n 10)) (if (= n 0) 0 (loop n)))")))
  (assert-violation-count "named-let with base case but no decrease" 1 violations)
  (assert-equal "named-let base-but-no-decrease kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; ============================================================
;; Test Group: Named-let analysis - no base case
;; ============================================================
(display "=== Named-let analysis: no base case ===") (newline)

;; Issue #273 test 3: decreasing but no base case
(let ((violations (check-source-termination
                    "(let loop ((n 10)) (loop (- n 1)))")))
  (assert-violation-count "named-let with decrease but no base case" 1 violations)
  (assert-equal "named-let no-base-case kind"
    'no-base-case
    (termination-violation-kind (car violations)))
  (assert-equal "named-let no-base-case function is loop name"
    'loop
    (termination-violation-function (car violations))))

(let ((violations (check-source-termination
                    "(let loop ((lst '(1 2 3))) (display (car lst)) (loop (cdr lst)))")))
  (assert-violation-count "named-let structural decrease but no base case" 1 violations)
  (assert-equal "named-let structural no-base-case kind"
    'no-base-case
    (termination-violation-kind (car violations))))

;; ============================================================
;; Test Group: Named-let analysis - infinite loop (no args)
;; ============================================================
(display "=== Named-let analysis: infinite loop ===") (newline)

(let ((violations (check-source-termination
                    "(let loop () (display \"forever\") (loop))")))
  (assert-violation-count "named-let with no args is infinite" 1 violations)
  (assert-equal "named-let no-args kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; ============================================================
;; Test Group: Named-let analysis - nested named-lets
;; ============================================================
(display "=== Named-let analysis: nested ===") (newline)

(assert-no-violations "nested valid named-lets"
  (check-source-termination
    "(let outer ((i 10)) (if (<= i 0) 0 (let inner ((j 5)) (if (<= j 0) (outer (- i 1)) (inner (- j 1))))))"))

(let ((violations (check-source-termination
                    "(let outer ((i 10)) (if (= i 0) 0 (let inner ((j 5)) (inner j))))")))
  (assert-violation-count "nested: inner invalid, outer valid" 1 violations))

;; ============================================================
;; Test Group: Named-let analysis - non-recursive named-let (no violations)
;; ============================================================
(display "=== Named-let analysis: non-recursive ===") (newline)

(assert-no-violations "named-let that doesn't recurse"
  (check-source-termination
    "(let loop ((x 1) (y 2)) (+ x y))"))

;; ============================================================
;; Test Group: Conservative fix 1 - no permissive if-alternative base case
;; ============================================================
(display "=== Conservative: if-alternative not counted as base case ===") (newline)

;; An if with opaque test and non-recursive alternative should NOT count as base case
(let ((violations (check-source-termination
                    "(let loop ((n 10)) (if (some-check) (loop (- n 1)) 42))")))
  (assert-violation-count "if with opaque test and non-recursive alt flagged" 1 violations)
  (assert-equal "opaque if-alt violation kind"
    'no-base-case
    (termination-violation-kind (car violations))))

;; Verify that recognized base-case tests still work (consequent path)
(assert-no-violations "if with recognized base-case test still passes"
  (check-source-termination
    "(let loop ((n 10)) (if (<= n 0) 0 (loop (- n 1))))"))

;; ============================================================
;; Test Group: Conservative fix 2 - when/unless test must reference loop var
;; ============================================================
(display "=== Conservative: when/unless test must reference loop var ===") (newline)

;; (when #t ...) should NOT count as having a base case
(let ((violations (check-source-termination
                    "(let loop ((n 10)) (when #t (loop (- n 1))))")))
  (assert-violation-count "when #t with recursive body flagged" 1 violations)
  (assert-equal "when #t violation kind"
    'no-base-case
    (termination-violation-kind (car violations))))

;; (when (some-opaque-check) ...) should NOT count as base case
(let ((violations (check-source-termination
                    "(let loop ((n 10)) (when (some-opaque-check) (loop (- n 1))))")))
  (assert-violation-count "when with opaque test flagged" 1 violations)
  (assert-equal "when opaque-test violation kind"
    'no-base-case
    (termination-violation-kind (car violations))))

;; (unless #f ...) should NOT count as having a base case
(let ((violations (check-source-termination
                    "(let loop ((n 10)) (unless #f (loop (- n 1))))")))
  (assert-violation-count "unless #f with recursive body flagged" 1 violations)
  (assert-equal "unless #f violation kind"
    'no-base-case
    (termination-violation-kind (car violations))))

;; Verify that when/unless with test referencing loop var still work
(assert-no-violations "when with test referencing loop var still passes"
  (check-source-termination
    "(let loop ((n 10)) (when (> n 0) (display n) (loop (- n 1))))"))

(assert-no-violations "unless with test referencing loop var still passes"
  (check-source-termination
    "(let loop ((n 10)) (unless (<= n 0) (display n) (loop (- n 1))))"))

;; ============================================================
;; Test Group: Conservative fix 3 - all recursive calls must decrease
;; ============================================================
(display "=== Conservative: all calls must decrease ===") (newline)

;; Mixed: one decreasing call + one non-decreasing call → should be flagged
(let ((violations (check-source-termination
                    "(let loop ((x 10)) (if (zero? x) 'done (begin (loop (- x 1)) (loop x))))")))
  (assert-violation-count "mixed decreasing/non-decreasing calls flagged" 1 violations)
  (assert-equal "mixed calls violation kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; All calls decrease → should pass
(assert-no-violations "all calls decrease passes"
  (check-source-termination
    "(let loop ((x 10)) (if (<= x 0) 'done (if (even? x) (loop (- x 1)) (loop (- x 2)))))"))

;; Single non-decreasing call → should be flagged (same as before)
(let ((violations (check-source-termination
                    "(let loop ((n 10)) (if (= n 0) 0 (loop n)))")))
  (assert-violation-count "single non-decreasing call still flagged" 1 violations)
  (assert-equal "single non-decrease kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; ============================================================
;; Test Group: Direct recursion analysis - valid forms (no violations)
;; ============================================================
(display "=== Direct recursion analysis: valid ===") (newline)

;; Issue #274 test 1: factorial with numeric decrease + base case
(assert-no-violations "direct recursion: factorial passes"
  (check-source-termination
    "(define (fact n) (if (<= n 0) 1 (* n (fact (- n 1)))))"))

;; Issue #274 test 3: structural decrease with cdr
(assert-no-violations "direct recursion: list length passes"
  (check-source-termination
    "(define (f xs) (if (null? xs) 0 (+ 1 (f (cdr xs)))))"))

;; Issue #274 test 4: fibonacci with two recursive calls
(assert-no-violations "direct recursion: fibonacci passes"
  (check-source-termination
    "(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))"))

;; Multi-arg: at least one arg decreases
(assert-no-violations "direct recursion: multi-arg with one decreasing"
  (check-source-termination
    "(define (f x y) (if (null? x) y (f (cdr x) (+ y 1))))"))

;; Non-recursive function should produce no violations
(assert-no-violations "direct recursion: non-recursive function passes"
  (check-source-termination
    "(define (add x y) (+ x y))"))

;; define-lambda form
(assert-no-violations "direct recursion: define-lambda factorial passes"
  (check-source-termination
    "(define fact (lambda (n) (if (<= n 0) 1 (* n (fact (- n 1))))))"))

;; letrec-bound recursive function with decrease + base case
(assert-no-violations "direct recursion: letrec with decrease + base passes"
  (check-source-termination
    "(letrec ((f (lambda (n) (if (<= n 0) 0 (f (- n 1)))))) (f 10))"))

;; sub1 decrease pattern
(assert-no-violations "direct recursion: sub1 decrease passes"
  (check-source-termination
    "(define (count n) (if (<= n 0) 0 (count (sub1 n))))"))

;; cond-based base case
(assert-no-violations "direct recursion: cond base case passes"
  (check-source-termination
    "(define (f n) (cond ((<= n 0) 0) (else (f (- n 1)))))"))

;; ============================================================
;; Test Group: Direct recursion analysis - violations
;; ============================================================
(display "=== Direct recursion analysis: violations ===") (newline)

;; Issue #274 test 2: no decrease, no base case
(let ((violations (check-source-termination
                    "(define (f n) (f n))")))
  (assert-violation-count "direct recursion: no decrease no base" 1 violations)
  (assert-equal "direct recursion no-decrease kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations)))
  (assert-equal "direct recursion no-decrease function"
    'f
    (termination-violation-function (car violations))))

;; Increasing argument with lower-bound base case (unsound: increasing away from zero)
(let ((violations (check-source-termination
                    "(define (f n) (if (zero? n) 0 (f (+ n 1))))")))
  (assert-violation-count "direct recursion: increasing arg" 1 violations)
  (assert-equal "direct recursion increasing-arg kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; Decrease but no base case
(let ((violations (check-source-termination
                    "(define (f n) (f (- n 1)))")))
  (assert-violation-count "direct recursion: decrease but no base" 1 violations)
  (assert-equal "direct recursion no-base kind"
    'no-base-case
    (termination-violation-kind (car violations))))

;; Base case exists but no decrease in recursive call
(let ((violations (check-source-termination
                    "(define (f n) (if (zero? n) 0 (f n)))")))
  (assert-violation-count "direct recursion: base but no decrease" 1 violations)
  (assert-equal "direct recursion base-no-decrease kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; letrec-bound with no decrease
(let ((violations (check-source-termination
                    "(letrec ((f (lambda (n) (f n)))) (f 10))")))
  (assert-violation-count "direct recursion: letrec no decrease" 1 violations)
  (assert-equal "direct recursion letrec no-decrease kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; ============================================================
;; Test Group: Direct recursion analysis - conservative behavior
;; ============================================================
(display "=== Direct recursion analysis: conservative ===") (newline)

;; Higher-order: function passed as argument -- should NOT be flagged
(assert-no-violations "direct recursion: higher-order not flagged"
  (check-source-termination
    "(define (apply-f f x) (f x))"))

;; Mutual recursion handled by Phase 6 -- valid patterns should not produce violations here
(assert-no-violations "direct recursion: mutual recursion handled by Phase 6"
  (check-source-termination
    "(define (even? n) (if (<= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (<= n 0) #f (even? (- n 1))))"))

;; ============================================================
;; Test Group: Mutual recursion analysis - valid patterns (no violations)
;; ============================================================
(display "=== Mutual recursion analysis: valid ===") (newline)

;; Issue #275 test 1: even?/odd? with (- n 1) and base cases
(assert-no-violations "mutual recursion: even?/odd? with decrease and base case"
  (check-source-termination
    (string-append
      "(define (my-even? n) (if (<= n 0) #t (my-odd? (- n 1)))) "
      "(define (my-odd? n) (if (<= n 0) #f (my-even? (- n 1))))")))

;; Three-function cycle all decreasing
(assert-no-violations "mutual recursion: three-function cycle with decrease"
  (check-source-termination
    (string-append
      "(define (a n) (if (<= n 0) 'done (b (- n 1)))) "
      "(define (b n) (if (<= n 0) 'done (c (- n 1)))) "
      "(define (c n) (if (<= n 0) 'done (a (- n 1))))")))

;; Both functions decrease on their respective calls
(assert-no-violations "mutual recursion: both functions decrease before calling partner"
  (check-source-termination
    (string-append
      "(define (ping n) (if (<= n 0) 'done (pong (- n 1)))) "
      "(define (pong n) (if (<= n 0) 'done (ping (- n 1))))")))

;; letrec-bound mutual recursion
(assert-no-violations "mutual recursion: letrec-bound even/odd"
  (check-source-termination
    (string-append
      "(letrec ((ev (lambda (n) (if (<= n 0) #t (od (- n 1))))) "
      "         (od (lambda (n) (if (<= n 0) #f (ev (- n 1)))))) "
      "  (ev 10))")))

;; Structural decrease (cdr) in mutual recursion
(assert-no-violations "mutual recursion: structural decrease with cdr"
  (check-source-termination
    (string-append
      "(define (process-a lst) (if (null? lst) '() (process-b (cdr lst)))) "
      "(define (process-b lst) (if (null? lst) '() (process-a (cdr lst))))")))

;; ============================================================
;; Test Group: Mutual recursion analysis - violations
;; ============================================================
(display "=== Mutual recursion analysis: violations ===") (newline)

;; Issue #275 test 2: mutual recursion without decrease -- flag both
(let ((violations (check-source-termination
                    (string-append
                      "(define (ping n) (pong n)) "
                      "(define (pong n) (ping n))"))))
  (assert-violation-count "mutual recursion: no decrease flags both" 2 violations)
  (assert-equal "mutual recursion no-decrease kind (first)"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; Mutual recursion with decrease but no base case
(let ((violations (check-source-termination
                    (string-append
                      "(define (down-a n) (down-b (- n 1))) "
                      "(define (down-b n) (down-a (- n 1)))"))))
  (assert-violation-count "mutual recursion: decrease but no base case flags both" 2 violations)
  (assert-equal "mutual recursion no-base-case kind"
    'no-base-case
    (termination-violation-kind (car violations))))

;; Partial decrease: one decreases, other doesn't and doesn't receive decreased value
;; Here ping decreases but pong passes n unchanged back (not the decreased value)
(let ((violations (check-source-termination
                    (string-append
                      "(define (alpha n) (if (= n 0) 'done (beta n))) "
                      "(define (beta n) (alpha n))"))))
  (assert-violation-count "mutual recursion: no edge decreases flags both" 2 violations))

;; Self-loop within multi-node SCC: f calls itself AND g (which calls f)
;; The self-call doesn't decrease -- should flag the group
(let ((violations (check-source-termination
                    (string-append
                      "(define (loop-a n) (loop-a n) (loop-b (- n 1))) "
                      "(define (loop-b n) (if (= n 0) 'done (loop-a (- n 1))))"))))
  (assert-violation-count "mutual recursion: self-loop without decrease in SCC" 2 violations))

;; ============================================================
;; Test Group: Integration and edge cases (Phase 7)
;; ============================================================
(display "=== Integration and edge cases ===") (newline)

;; 1a. Non-recursive programs produce no violations
(assert-no-violations "non-recursive: plain defines and lambdas"
  (check-source-termination
    "(define (add x y) (+ x y)) (define (greet name) (string-append \"Hello \" name))"))

(assert-no-violations "non-recursive: higher-order functions"
  (check-source-termination
    "(define (apply-twice f x) (f (f x))) (apply-twice add1 5)"))

(assert-no-violations "non-recursive: let/let* without recursion"
  (check-source-termination
    "(let ((x 1) (y 2)) (+ x y))"))

(assert-no-violations "non-recursive: nested lambdas"
  (check-source-termination
    "(define (make-adder n) (lambda (x) (+ x n)))"))

;; 1b. Multiple violations in one program
(let ((violations (check-source-termination
                    (string-append
                      "(do ((i 0 (+ i 1))) (#f) (display i)) "
                      "(let loop () (loop)) "
                      "(define (f n) (f n))"))))
  (assert-violation-count "multiple violations: 3 different kinds" 3 violations))

;; 1c. Mix of safe loops and unsafe recursion -- only unsafe flagged
(let ((violations (check-source-termination
                    (string-append
                      ;; Safe: named-let with decrease and base case
                      "(define (countdown n) (let loop ((i n)) (if (<= i 0) 'done (loop (- i 1))))) "
                      ;; Unsafe: direct recursion with no decrease
                      "(define (spin n) (spin n))"))))
  (assert-violation-count "mixed safe/unsafe: only unsafe flagged" 1 violations)
  (assert-equal "mixed safe/unsafe: violation is for 'spin'"
    'spin
    (termination-violation-function (car violations))))

;; 1d. Nested recursion -- recursive function inside a let inside another recursive function
(let ((violations (check-source-termination
                    (string-append
                      "(define (outer n) "
                      "  (let ((inner (lambda (m) (if (<= m 0) 'done (inner (- m 1)))))) "
                      "    (if (<= n 0) 'base (outer (- n 1)))))"))))
  ;; outer is safe (has base case and decreasing arg)
  ;; inner: lambda named 'inner' -- depends on whether letrec binding is detected
  ;; At minimum, outer should not be flagged
  (let ((outer-violations (filter (lambda (v) (eq? (termination-violation-function v) 'outer))
                                  violations)))
    (assert-no-violations "nested recursion: outer is safe" outer-violations)))

;; 1e. Zero false positives on sample-safe.ss patterns (fibonacci and factorial)
(assert-no-violations "sample-safe: fibonacci via named-let"
  (check-source-termination
    (string-append
      "(define (fibonacci n) "
      "  (let loop ((i 0) (a 0) (b 1)) "
      "    (if (= i n) a (loop (+ i 1) b (+ a b)))))")))

(assert-no-violations "sample-safe: factorial via letrec"
  (check-source-termination
    (string-append
      "(define (factorial n) "
      "  (letrec ((fact (lambda (n acc) "
      "                   (if (<= n 0) acc (fact (- n 1) (* acc n)))))) "
      "    (fact n 1)))")))

;; 1f. Correctly flags known infinite loops
(let ((violations (check-source-termination
                    "(do ((i 0 (+ i 1))) (#f) (display i))")))
  (assert-violation-count "infinite do-loop: always-false test" 1 violations)
  (assert-equal "infinite do-loop kind"
    'infinite-loop
    (termination-violation-kind (car violations))))

(let ((violations (check-source-termination
                    "(define (f n) (f n))")))
  (assert-violation-count "no-decrease direct recursion" 1 violations)
  (assert-equal "no-decrease kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

(let ((violations (check-source-termination
                    "(let loop () (loop))")))
  (assert-violation-count "named-let with no args always flags" 1 violations)
  (assert-equal "named-let no-args kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; 1g. Recursion on decreasing list (tool-call use case)
(assert-no-violations "list recursion: cdr with null? base case"
  (check-source-termination
    (string-append
      "(define (process-records records) "
      "  (if (null? records) '() "
      "    (begin (car records) (process-records (cdr records)))))")))

;; ============================================================
;; Test Group: Depth limit (Phase 7)
;; ============================================================
(display "=== Depth limit ===") (newline)

;; check-termination with depth limit of 0 should block programs that exceed it
;; (definition count 1 > limit 0 → definition-limit-exceeded violation)
(let ((violations (check-termination
                    (read-all-expressions "(define (f n) (f n))")
                    '()
                    '()
                    0)))  ;; depth-limit = 0 blocks any program with definitions
  (assert-true "depth-limit 0: emits definition-limit-exceeded"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'definition-limit-exceeded))
            violations)))

;; Depth limit that is not exceeded allows normal analysis
(let ((violations (check-termination
                    (read-all-expressions "(define (f n) (f n))")
                    '()
                    '()
                    10)))  ;; depth-limit = 10, only 1 definition → not exceeded
  (assert-true "depth-limit not exceeded: catches direct recursion"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'no-decreasing-arg))
            violations)))

;; With no depth limit (default), direct recursion is caught
(let ((violations (check-termination
                    (read-all-expressions "(define (f n) (f n))")
                    '())))
  (assert-violation-count "no depth-limit: catches direct recursion" 1 violations))

;; ============================================================
;; Test Group: Collection HOF whitelist
;; ============================================================
(display "=== Collection HOF whitelist ===") (newline)

;; collection-hof? recognizes standard HOFs
(assert-true "collection-hof? recognizes map"
  (collection-hof? 'map))
(assert-true "collection-hof? recognizes fold-left"
  (collection-hof? 'fold-left))
(assert-true "collection-hof? recognizes filter"
  (collection-hof? 'filter))
(assert-true "collection-hof? recognizes for-each"
  (collection-hof? 'for-each))
(assert-true "collection-hof? recognizes vector-map"
  (collection-hof? 'vector-map))

;; collection-hof? rejects non-HOFs
(assert-equal "collection-hof? rejects unknown"
  #f
  (collection-hof? 'my-custom-map))
(assert-equal "collection-hof? rejects car"
  #f
  (collection-hof? 'car))

;; HOF calls do not generate call graph edges.
;; Note: (map helper lst) — 'helper' is in argument position, not call position,
;; so it correctly does not appear as a call graph edge. This is a known
;; limitation: callback functions passed to HOFs are not tracked as calls.
(let ((graph (source->call-graph
               (string-append
                 "(define (process lst) (map helper lst)) "
                 "(define (helper x) (+ x 1))"))))
  (assert-equal "process has no call edges (helper is in arg position)"
    '()
    (call-graph-edges graph 'process)))

;; When helper is directly called, it appears as an edge
(let ((graph (source->call-graph
               (string-append
                 "(define (process lst) (helper (car lst))) "
                 "(define (helper x) (+ x 1))"))))
  (assert-true "process calls helper (direct call)"
    (list-contains? (call-graph-edges graph 'process) 'helper)))

;; User-defined function named 'map' that collides with HOF whitelist:
;; Since collect-calls-in-body filters by HOF name AND target-names,
;; a user-defined 'map' would be excluded from call graph edges.
;; This is the documented known limitation for HOF callback tracking.

;; ============================================================
;; Test Group: HOF whitelist - termination check (positive)
;; ============================================================
(display "=== HOF whitelist: no violations ===") (newline)

;; Direct calls to whitelisted HOFs should not trigger termination warnings
(assert-no-violations "map call does not trigger warning"
  (check-source-termination "(define (f lst) (map car lst))"))

(assert-no-violations "fold-left call does not trigger warning"
  (check-source-termination "(define (sum lst) (fold-left + 0 lst))"))

(assert-no-violations "filter call does not trigger warning"
  (check-source-termination "(define (evens lst) (filter even? lst))"))

(assert-no-violations "for-each call does not trigger warning"
  (check-source-termination "(define (print-all lst) (for-each display lst))"))

(assert-no-violations "find call does not trigger warning"
  (check-source-termination "(define (first-even lst) (find even? lst))"))

(assert-no-violations "exists call does not trigger warning"
  (check-source-termination "(define (has-zero? lst) (exists zero? lst))"))

(assert-no-violations "vector-map call does not trigger warning"
  (check-source-termination "(define (inc-vec v) (vector-map add1 v))"))

(assert-no-violations "nested HOF calls do not trigger warning"
  (check-source-termination
    "(define (process lst) (map car (filter pair? lst)))"))

;; HOF used inside recursive function that is itself terminating
(assert-no-violations "HOF inside terminating recursive function"
  (check-source-termination
    (string-append
      "(define (process-tree node) "
      "  (if (null? node) '() "
      "    (append (map process-tree (cdr node)) (list (car node)))))"))
  )

;; ============================================================
;; Test Group: Type-env lookup
;; ============================================================
(display "=== Type-env lookup ===") (newline)

(let ((env (list (cons 'x type:number) (cons 'lst (make-type-list type:number)))))
  (assert-true "type-env-lookup finds number type"
    (type=? type:number (type-env-lookup env 'x)))
  (assert-true "type-env-lookup finds list type"
    (type-list? (type-env-lookup env 'lst)))
  (assert-equal "type-env-lookup returns #f for missing var"
    #f
    (type-env-lookup env 'y)))

;; ============================================================
;; Test Group: Type-aware termination (positive - with type-env)
;; ============================================================
(display "=== Type-aware termination: positive ===") (newline)

;; Named-let list traversal with type-env providing (List Number)
(let* ((type-env (list (cons 'lst (make-type-list type:number))))
       (exprs (read-all-expressions
                "(let loop ((lst lst)) (if (null? lst) 0 (+ (car lst) (loop (cdr lst)))))"))
       (violations (check-termination exprs type-env)))
  (assert-no-violations "typed list traversal via named-let" violations))

;; Direct recursion over typed list parameter
(let* ((type-env (list (cons 'xs (make-type-list type:string))))
       (exprs (read-all-expressions
                "(define (count xs) (if (null? xs) 0 (+ 1 (count (cdr xs)))))"))
       (violations (check-termination exprs type-env)))
  (assert-no-violations "typed list recursion: count" violations))

;; Accumulator pattern with typed list
(let* ((type-env (list (cons 'lst (make-type-list type:number))))
       (exprs (read-all-expressions
                "(let loop ((lst lst) (acc 0)) (if (null? lst) acc (loop (cdr lst) (+ acc (car lst)))))"))
       (violations (check-termination exprs type-env)))
  (assert-no-violations "typed list accumulator pattern" violations))

;; ============================================================
;; Test Group: Type-aware termination (negative - violations expected)
;; ============================================================
(display "=== Type-aware termination: negative ===") (newline)

;; No decrease, no base case (type info doesn't help)
(let* ((type-env (list (cons 'x type:number)))
       (exprs (read-all-expressions
                "(let loop ((x (get-items))) (loop x))"))
       (violations (check-termination exprs type-env)))
  (assert-violation-count "no decrease even with type info" 1 violations)
  (assert-equal "no-decrease-with-type kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; Decrease without base case (type info doesn't add missing base case)
(let* ((type-env (list (cons 'n type:number)))
       (exprs (read-all-expressions
                "(let loop ((n 10)) (loop (- n 1)))"))
       (violations (check-termination exprs type-env)))
  (assert-violation-count "decrease but no base case with type info" 1 violations)
  (assert-equal "no-base-with-type kind"
    'no-base-case
    (termination-violation-kind (car violations))))

;; Direct recursion without decrease (type info doesn't help)
(let* ((type-env (list (cons 'n type:number)))
       (exprs (read-all-expressions
                "(define (f n) (f n))"))
       (violations (check-termination exprs type-env)))
  (assert-violation-count "direct recursion no decrease with type" 1 violations))

;; Mutual recursion without decrease
(let* ((type-env (list (cons 'n type:number)))
       (exprs (read-all-expressions
                (string-append
                  "(define (ping n) (pong n)) "
                  "(define (pong n) (ping n))")))
       (violations (check-termination exprs type-env)))
  (assert-violation-count "mutual recursion no decrease with type" 2 violations))

;; Named-let typed list traversal with decrease but no base case
;; Type info should NOT suppress no-base-case when guard is missing
(let* ((type-env (list (cons 'lst (make-type-list type:number))))
       (exprs (read-all-expressions
                "(let loop ((lst lst)) (loop (cdr lst)))"))
       (violations (check-termination exprs type-env)))
  (assert-violation-count "typed list decrease but no base case (named-let)" 1 violations)
  (assert-equal "typed list no-base-case kind (named-let)"
    'no-base-case
    (termination-violation-kind (car violations))))

;; Direct recursion over typed list parameter with decrease but no base case
(let* ((type-env (list (cons 'xs (make-type-list type:number))))
       (exprs (read-all-expressions
                "(define (f xs) (f (cdr xs)))"))
       (violations (check-termination exprs type-env)))
  (assert-violation-count "typed list decrease but no base case (direct)" 1 violations)
  (assert-equal "typed list no-base-case kind (direct)"
    'no-base-case
    (termination-violation-kind (car violations))))

;; Zero-variable named-let
(let* ((type-env '())
       (exprs (read-all-expressions "(let loop () (loop))"))
       (violations (check-termination exprs type-env)))
  (assert-violation-count "zero-variable loop still flagged with empty type-env" 1 violations))

;; ============================================================
;; Test Group: Type-env interaction (same code, with and without types)
;; ============================================================
(display "=== Type-env interaction ===") (newline)

;; This code should pass even without type info (syntactic analysis catches it)
(let* ((exprs (read-all-expressions
                "(let loop ((lst '(1 2 3))) (if (null? lst) 0 (loop (cdr lst))))"))
       (violations-no-type (check-termination exprs '()))
       (violations-typed (check-termination exprs
                           (list (cons 'lst (make-type-list type:number))))))
  (assert-no-violations "list traversal passes without type-env" violations-no-type)
  (assert-no-violations "list traversal passes with type-env" violations-typed))

;; This code should fail regardless of type info
(let* ((exprs (read-all-expressions "(let loop ((n 10)) (loop n))"))
       (violations-no-type (check-termination exprs '()))
       (violations-typed (check-termination exprs
                           (list (cons 'n type:number)))))
  (assert-violation-count "no-decrease fails without type" 1 violations-no-type)
  (assert-violation-count "no-decrease fails with type" 1 violations-typed))

;; ============================================================
;; Test Group: Record type termination (linked-list traversal)
;; ============================================================
(display "=== Record type termination ===") (newline)

;; Linked-list pattern: record with nullable self-reference
;; node type: (Record ((value . Number) (next . (U (Record ...) Null))))
;; For simplicity, we use a non-recursive union with Null
(let* ((node-type (make-type-record
                    (list (cons 'value type:number)
                          (cons 'next (make-type-union (list type:any type:null))))
                    '(value next)))
       (type-env (list (cons 'n node-type)))
       ;; Direct recursion: (define (traverse n) (if (null? n) '() (traverse (node-next n))))
       (exprs (read-all-expressions
                "(define (traverse n) (if (null? n) '() (traverse (node-next n))))"))
       (violations (check-termination exprs type-env)))
  (assert-no-violations "record linked-list traversal with type-env" violations))

;; Same code without type-env should fail (syntactic analysis doesn't know node-next is decreasing)
(let* ((exprs (read-all-expressions
                "(define (traverse n) (if (null? n) '() (traverse (node-next n))))"))
       (violations (check-termination exprs '())))
  (assert-violation-count "record traversal without type-env flagged" 1 violations)
  (assert-equal "record traversal no-type violation kind"
    'no-decreasing-arg
    (termination-violation-kind (car violations))))

;; Named-let with record traversal
(let* ((node-type (make-type-record
                    (list (cons 'value type:number)
                          (cons 'next (make-type-union (list type:any type:null))))
                    '(value next)))
       (type-env (list (cons 'node node-type)))
       (exprs (read-all-expressions
                "(let loop ((node node)) (if (null? node) 0 (+ (node-value node) (loop (node-next node)))))"))
       (violations (check-termination exprs type-env)))
  (assert-no-violations "named-let record traversal with type-env" violations))

;; Suffix ambiguity: record with fields "name" and "full-name"
;; accessor "node-full-name" should match "full-name" (longer), not "name"
(let* ((node-type (make-type-record
                    (list (cons 'name type:string)
                          (cons 'full-name (make-type-union (list type:any type:null)))
                          (cons 'next (make-type-union (list type:any type:null))))
                    '(name full-name next)))
       (type-env (list (cons 'n node-type)))
       ;; Traversal using node-full-name — should resolve to full-name (nullable) not name
       (exprs (read-all-expressions
                "(define (traverse n) (if (null? n) '() (traverse (node-full-name n))))"))
       (violations (check-termination exprs type-env)))
  (assert-no-violations "suffix ambiguity: longest match resolves node-full-name to full-name" violations))

;; ============================================================
;; Test Group: HOF callback position metadata
;; ============================================================
(display "=== HOF callback position metadata ===") (newline)

(assert-equal "hof-callback-position: map has callback at position 0"
  0
  (hof-callback-position 'map))

(assert-equal "hof-callback-position: fold-left has callback at position 0"
  0
  (hof-callback-position 'fold-left))

(assert-equal "hof-callback-position: filter has callback at position 0"
  0
  (hof-callback-position 'filter))

(assert-equal "hof-callback-position: vector-map has callback at position 0"
  0
  (hof-callback-position 'vector-map))

;; HOFs with no callback (use eq?/eqv? internally)
(assert-equal "hof-callback-position: memv has no callback"
  #f
  (hof-callback-position 'memv))

(assert-equal "hof-callback-position: memq has no callback"
  #f
  (hof-callback-position 'memq))

(assert-equal "hof-callback-position: remv has no callback"
  #f
  (hof-callback-position 'remv))

(assert-equal "hof-callback-position: assoc has no callback"
  #f
  (hof-callback-position 'assoc))

(assert-equal "hof-callback-position: unknown symbol returns #f"
  #f
  (hof-callback-position 'my-custom-fn))

;; ============================================================
;; Test Group: collect-hof-callback-edges
;; ============================================================
(display "=== collect-hof-callback-edges ===") (newline)

;; (map f lst) -> edge from caller to f
(let ((edges (collect-hof-callback-edges
               (read-all-expressions "(map helper lst)")
               'process)))
  (assert-equal "collect-hof-callback-edges: map with symbol callback"
    '((process . helper))
    edges))

;; (map (lambda (x) (+ x 1)) lst) -> no edges (lambda, not symbol)
(let ((edges (collect-hof-callback-edges
               (read-all-expressions "(map (lambda (x) (+ x 1)) lst)")
               'process)))
  (assert-equal "collect-hof-callback-edges: map with lambda callback"
    '()
    edges))

;; (memq val lst) -> no edges (no callback position)
(let ((edges (collect-hof-callback-edges
               (read-all-expressions "(memq val lst)")
               'process)))
  (assert-equal "collect-hof-callback-edges: memq has no callback edge"
    '()
    edges))

;; (fold-left combine init lst) -> edge from caller to combine
(let ((edges (collect-hof-callback-edges
               (read-all-expressions "(fold-left combine 0 lst)")
               'accum)))
  (assert-equal "collect-hof-callback-edges: fold-left with symbol callback"
    '((accum . combine))
    edges))

;; nested HOF calls: (map f (filter g lst))
(let ((edges (collect-hof-callback-edges
               (read-all-expressions "(map f (filter g lst))")
               'process)))
  (assert-true "collect-hof-callback-edges: nested HOFs produce two edges"
    (= 2 (length edges)))
  (assert-true "collect-hof-callback-edges: nested HOFs include f and g"
    (let ((cbs (map cdr edges)))
      (and (memq 'f cbs) (memq 'g cbs) #t))))

;; ============================================================
;; Test Group: HOF callback termination (positive - no violations)
;; ============================================================
(display "=== HOF callback termination: positive ===") (newline)

;; Safe user-defined callback: (map safe-fn lst) where safe-fn is non-recursive
(assert-no-violations "HOF with safe user-defined callback"
  (check-source-termination
    (string-append
      "(define (process lst) (map safe-fn lst)) "
      "(define (safe-fn x) (+ x 1))")))

;; Built-in callback: (map car lst) -- car is not in defined-names, so skipped
(assert-no-violations "HOF with built-in callback"
  (check-source-termination
    "(define (process lst) (map car lst))"))

;; Inline lambda callback -- no symbol resolution needed
(assert-no-violations "HOF with inline lambda callback"
  (check-source-termination
    "(define (process lst) (map (lambda (x) (+ x 1)) lst))"))

;; Callback that is not in user-defined set (unresolvable) -- assumed safe
(assert-no-violations "HOF with unresolvable callback symbol"
  (check-source-termination
    "(define (process lst) (map mystery-fn lst))"))

;; HOF with no callback position (memq, assq etc.)
(assert-no-violations "memq does not trigger callback check"
  (check-source-termination
    "(define (find-it lst) (memq 'x lst))"))

(assert-no-violations "assq does not trigger callback check"
  (check-source-termination
    "(define (lookup lst) (assq 'key lst))"))

;; Terminating recursive callback used in HOF
(assert-no-violations "HOF with terminating recursive callback"
  (check-source-termination
    (string-append
      "(define (process lst) (map my-length lst)) "
      "(define (my-length xs) (if (null? xs) 0 (+ 1 (my-length (cdr xs)))))")))

;; ============================================================
;; Test Group: HOF callback termination (negative - violations)
;; ============================================================
(display "=== HOF callback termination: negative ===") (newline)

;; Non-terminating callback: (map infinite-fn lst) where infinite-fn has unbounded recursion
(let ((violations
        (check-source-termination
          (string-append
            "(define (process lst) (map infinite-fn lst)) "
            "(define (infinite-fn x) (infinite-fn x))"))))
  ;; infinite-fn gets flagged for no-decreasing-arg AND process gets
  ;; flagged for hof-callback-not-terminating
  (assert-true "non-terminating callback: at least one hof-callback violation"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'hof-callback-not-terminating))
            violations))
  (assert-true "non-terminating callback: violation names process as caller"
    (exists (lambda (v)
              (and (eq? (termination-violation-kind v) 'hof-callback-not-terminating)
                   (eq? (termination-violation-function v) 'process)))
            violations)))

;; fold-left with non-terminating callback
(let ((violations
        (check-source-termination
          (string-append
            "(define (accum lst) (fold-left bad-fn 0 lst)) "
            "(define (bad-fn acc x) (bad-fn acc x))"))))
  (assert-true "fold-left with non-terminating callback flagged"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'hof-callback-not-terminating))
            violations)))

;; filter with non-terminating predicate
(let ((violations
        (check-source-termination
          (string-append
            "(define (select lst) (filter bad-pred lst)) "
            "(define (bad-pred x) (bad-pred x))"))))
  (assert-true "filter with non-terminating predicate flagged"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'hof-callback-not-terminating))
            violations)))

;; Mutually recursive non-terminating callback
(let ((violations
        (check-source-termination
          (string-append
            "(define (process lst) (map ping lst)) "
            "(define (ping x) (pong x)) "
            "(define (pong x) (ping x))"))))
  (assert-true "mutually recursive non-terminating callback flagged"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'hof-callback-not-terminating))
            violations)))

;; ============================================================
;; Test Group: User-defined HOF detection
;; ============================================================
(display "=== User-defined HOF detection ===") (newline)

;; detect-user-defined-hofs finds my-map as HOF with callback at position 0
(let* ((src (string-append
              "(define (my-map f lst) "
              "  (if (null? lst) '() "
              "      (cons (f (car lst)) (my-map f (cdr lst)))))"))
       (exprs (read-all-expressions src))
       (defs (extract-definitions exprs))
       (hofs (detect-user-defined-hofs defs exprs)))
  (assert-true "detect-user-defined-hofs: finds my-map"
    (and (assq 'my-map hofs) #t))
  (assert-equal "detect-user-defined-hofs: my-map callback at position 0"
    0
    (cdr (assq 'my-map hofs))))

;; detect-user-defined-hofs: non-HOF function (no param in call position)
(let* ((src "(define (add1 x) (+ x 1))")
       (exprs (read-all-expressions src))
       (defs (extract-definitions exprs))
       (hofs (detect-user-defined-hofs defs exprs)))
  (assert-equal "detect-user-defined-hofs: non-HOF returns empty"
    '()
    hofs))

;; detect-user-defined-hofs: callback at position 1
(let* ((src (string-append
              "(define (my-fold init f lst) "
              "  (if (null? lst) init "
              "      (my-fold (f init (car lst)) f (cdr lst))))"))
       (exprs (read-all-expressions src))
       (defs (extract-definitions exprs))
       (hofs (detect-user-defined-hofs defs exprs)))
  (assert-true "detect-user-defined-hofs: callback at position 1"
    (and (assq 'my-fold hofs)
         (= 1 (cdr (assq 'my-fold hofs))))))

;; collect-user-hof-callback-edges: finds callback passed to user-defined HOF
(let* ((src (string-append
              "(define (my-map f lst) "
              "  (if (null? lst) '() "
              "      (cons (f (car lst)) (my-map f (cdr lst))))) "
              "(define (helper x) (+ x 1)) "
              "(define (process data) (my-map helper data))"))
       (exprs (read-all-expressions src))
       (defs (extract-definitions exprs))
       (hofs (detect-user-defined-hofs defs exprs))
       (process-body (cdr (assq 'process defs)))
       (edges (collect-user-hof-callback-edges process-body 'process hofs)))
  (assert-true "collect-user-hof-callback-edges: finds helper via my-map"
    (exists (lambda (e)
              (and (eq? (car e) 'process)
                   (eq? (cadr e) 'my-map)
                   (eq? (caddr e) 'helper)))
            edges)))

;; ============================================================
;; Test Group: User-defined HOF callback termination (positive)
;; ============================================================
(display "=== User-defined HOF callback: positive ===") (newline)

;; Safe callback passed to user-defined HOF
(assert-no-violations "user HOF with safe callback"
  (check-source-termination
    (string-append
      "(define (my-map f lst) "
      "  (if (null? lst) '() "
      "      (cons (f (car lst)) (my-map f (cdr lst))))) "
      "(define (safe-fn x) (+ x 1)) "
      "(define (process data) (my-map safe-fn data))")))

;; Terminating recursive callback passed to user-defined HOF
(assert-no-violations "user HOF with terminating recursive callback"
  (check-source-termination
    (string-append
      "(define (my-map f lst) "
      "  (if (null? lst) '() "
      "      (cons (f (car lst)) (my-map f (cdr lst))))) "
      "(define (my-length xs) (if (null? xs) 0 (+ 1 (my-length (cdr xs))))) "
      "(define (process data) (my-map my-length data))")))

;; Built-in callback passed to user-defined HOF (not in defined-names)
(assert-no-violations "user HOF with built-in callback"
  (check-source-termination
    (string-append
      "(define (my-map f lst) "
      "  (if (null? lst) '() "
      "      (cons (f (car lst)) (my-map f (cdr lst))))) "
      "(define (process data) (my-map car data))")))

;; Inline lambda callback — no symbol resolution needed
(assert-no-violations "user HOF with inline lambda callback"
  (check-source-termination
    (string-append
      "(define (my-map f lst) "
      "  (if (null? lst) '() "
      "      (cons (f (car lst)) (my-map f (cdr lst))))) "
      "(define (process data) (my-map (lambda (x) (+ x 1)) data))")))

;; ============================================================
;; Test Group: User-defined HOF callback termination (negative)
;; ============================================================
(display "=== User-defined HOF callback: negative ===") (newline)

;; Non-terminating callback passed to user-defined HOF
(let ((violations
        (check-source-termination
          (string-append
            "(define (my-map f lst) "
            "  (if (null? lst) '() "
            "      (cons (f (car lst)) (my-map f (cdr lst))))) "
            "(define (dangerous-fn x) (dangerous-fn x)) "
            "(define (process data) (my-map dangerous-fn data))"))))
  (assert-true "user HOF with non-terminating callback: flagged"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'hof-callback-not-terminating))
            violations))
  (assert-true "user HOF violation names process as caller"
    (exists (lambda (v)
              (and (eq? (termination-violation-kind v) 'hof-callback-not-terminating)
                   (eq? (termination-violation-function v) 'process)))
            violations)))

;; Non-terminating HOF itself: only the HOF is flagged, not the callback path
(let ((violations
        (check-source-termination
          (string-append
            "(define (bad-map f lst) (bad-map f lst)) "
            "(define (safe-fn x) (+ x 1)) "
            "(define (process data) (bad-map safe-fn data))"))))
  ;; bad-map is flagged for no-decreasing-arg
  (assert-true "non-terminating user HOF: HOF itself flagged"
    (exists (lambda (v)
              (and (eq? (termination-violation-kind v) 'no-decreasing-arg)
                   (eq? (termination-violation-function v) 'bad-map)))
            violations))
  ;; safe-fn should NOT be flagged as hof-callback-not-terminating
  ;; (bad-map is not proven terminating, so its callbacks are not checked)
  (assert-true "non-terminating user HOF: callback NOT flagged"
    (not (exists (lambda (v)
                   (eq? (termination-violation-kind v) 'hof-callback-not-terminating))
                 violations))))

;; Mutually recursive non-terminating callback via user-defined HOF
(let ((violations
        (check-source-termination
          (string-append
            "(define (my-for-each f lst) "
            "  (if (null? lst) (void) "
            "      (begin (f (car lst)) (my-for-each f (cdr lst))))) "
            "(define (ping x) (pong x)) "
            "(define (pong x) (ping x)) "
            "(define (process data) (my-for-each ping data))"))))
  (assert-true "user HOF with mutually recursive callback: flagged"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'hof-callback-not-terminating))
            violations)))

;; ============================================================
;; Test Group: Vector index-based iteration (positive - no violations)
;; ============================================================
(display "=== Vector index iteration: positive ===") (newline)

;; Named-let increasing to vector-length with when/< guard
(assert-no-violations "named-let increasing index with when (< i (vector-length v))"
  (check-source-termination
    "(let loop ((i 0)) (when (< i (vector-length v)) (process (vector-ref v i)) (loop (+ i 1))))"))

;; Named-let increasing to vector-length with if/>= base case
(assert-no-violations "named-let increasing index with if (>= i (vector-length v))"
  (check-source-termination
    "(let loop ((i 0)) (if (>= i (vector-length v)) '() (begin (process (vector-ref v i)) (loop (+ i 1)))))"))

;; Named-let increasing with (= i (vector-length v)) base case
(assert-no-violations "named-let increasing index with (= i (vector-length v))"
  (check-source-termination
    "(let loop ((i 0)) (if (= i (vector-length v)) '() (begin (process (vector-ref v i)) (loop (+ i 1)))))"))

;; Named-let decreasing from (- (vector-length v) 1) with when/>= guard
(assert-no-violations "named-let decreasing from vector-length with when (>= i 0)"
  (check-source-termination
    "(let loop ((i (- (vector-length v) 1))) (when (>= i 0) (process (vector-ref v i)) (loop (- i 1))))"))

;; Do-form with increasing index
(assert-no-violations "do-form with increasing vector index"
  (check-source-termination
    "(do ((i 0 (+ i 1))) ((= i (vector-length v)) result) (process (vector-ref v i)))"))

;; Do-form with increasing index and >= test
(assert-no-violations "do-form with increasing index and >= test"
  (check-source-termination
    "(do ((i 0 (+ i 1))) ((>= i (vector-length v))) (process (vector-ref v i)))"))

;; add1 variant
(assert-no-violations "named-let with add1 step"
  (check-source-termination
    "(let loop ((i 0)) (if (= i (vector-length v)) '() (begin (process (vector-ref v i)) (loop (add1 i)))))"))

;; fx+ variant
(assert-no-violations "named-let with fx+ step"
  (check-source-termination
    "(let loop ((i 0)) (when (< i (vector-length v)) (process (vector-ref v i)) (loop (fx+ i 1))))"))

;; (> i N) bound test variant
(assert-no-violations "named-let with (> i (vector-length v)) base case"
  (check-source-termination
    "(let loop ((i 0)) (if (> i (vector-length v)) '() (begin (process (vector-ref v i)) (loop (+ i 1)))))"))

;; Direct recursion with increasing index (LLM-generated SRFI-1 style - #298 scenario)
(assert-no-violations "direct recursion: vector iteration with increasing index"
  (check-source-termination
    (string-append
      "(define (my-vector-map f v i) "
      "  (if (>= i (vector-length v)) "
      "      '() "
      "      (cons (f (vector-ref v i)) "
      "            (my-vector-map f v (+ i 1)))))")))

;; Direct recursion with = base case
(assert-no-violations "direct recursion: vector iteration with = base case"
  (check-source-termination
    (string-append
      "(define (vec-to-list v i) "
      "  (if (= i (vector-length v)) "
      "      '() "
      "      (cons (vector-ref v i) "
      "            (vec-to-list v (+ i 1)))))")))

;; ============================================================
;; Test Group: Vector index-based iteration (negative - violations)
;; ============================================================
(display "=== Vector index iteration: negative ===") (newline)

;; Increasing index with no base-case test
(let ((violations
        (check-source-termination
          (string-append
            "(define (bad-vec-iter v i) "
            "  (bad-vec-iter v (+ i 1)))"))))
  (assert-true "increasing index with no base case: flagged"
    (exists (lambda (v)
              (or (eq? (termination-violation-kind v) 'no-base-case)
                  (eq? (termination-violation-kind v) 'no-decreasing-arg)))
            violations)))

;; Increasing index with unrelated bound variable
(let ((violations
        (check-source-termination
          (string-append
            "(define (bad-bound v i) "
            "  (if (>= x (vector-length v)) "
            "      '() "
            "      (bad-bound v (+ i 1))))"))))
  (assert-true "increasing index with unrelated bound: flagged"
    (> (length violations) 0)))

;; No step expression at all (infinite loop)
(let ((violations
        (check-source-termination
          (string-append
            "(define (no-step v i) "
            "  (if (= i (vector-length v)) "
            "      '() "
            "      (no-step v i)))"))))
  (assert-true "no step expression: flagged as no-decreasing-arg"
    (exists (lambda (v)
              (eq? (termination-violation-kind v) 'no-decreasing-arg))
            violations)))

;; ============================================================
;; HC-2: higher-order call edges (0CFA)
;; ============================================================
;; Each loop below reaches its callee through a variable, an immediate
;; lambda or a built-in HOF, so a call graph built by name cannot see it.

(define (assert-rejected test-name source)
  (assert-true test-name
    (> (length (check-source-termination source)) 0)))

(assert-rejected "hc-2 omega: rejected"
  "((lambda (x) (x x)) (lambda (x) (x x)))")

(assert-rejected "hc-2 self-application through a formal: rejected"
  "(define (f g) (g g)) (f f)")

(assert-rejected "hc-2 alias through let: rejected"
  "(define (loop n) (let ((h loop)) (h n))) (loop 3)")

(assert-rejected "hc-2 recursion through map on a fresh list: rejected"
  "(define (f x) (map f (list x))) (f 1)")

(assert-rejected "hc-2 anonymous self-application inside a define: rejected"
  "(define (f) (let ((g (lambda (h) (h h)))) (g g))) (f)")

(assert-no-violations "hc-2 recursion through map on a formal: accepted"
  (check-source-termination
    "(define (tree-sum t) (if (not (pair? t)) t (apply + (map tree-sum t))))"))

(assert-no-violations "hc-2 nested for-each with decreasing self-call: accepted"
  (check-source-termination
    (string-append
      "(define (f n) "
      "  (if (<= n 0) 0 "
      "      (begin (for-each (lambda (x) (display x)) (list n)) "
      "             (f (- n 1)))))")))

;; fold-left hands its callback (acc elem): only the second formal receives
;; an element of the list, so a decrease must be proven in that position.
(assert-no-violations "hc-2 recursion through fold-left, element in its position: accepted"
  (check-source-termination
    "(define (count acc t) (if (not (pair? t)) (+ acc 1) (fold-left count acc t)))"))

(assert-rejected "hc-2 recursion through fold-left, element in the accumulator slot: rejected"
  "(define (f l acc) (if (not (pair? l)) acc (fold-left f acc l)))")

;; Step 4: cycles made only of anonymous lambdas, and fail-closed calls.

(assert-rejected "hc-2 omega with case-lambda clauses: rejected"
  "((case-lambda ((x) (x x))) (case-lambda ((x) (x x))))")

(assert-rejected "hc-2 two anonymous lambdas calling each other inside a define: rejected"
  "(define (f) (let ((a (lambda (p q) (p q p)))) (a a a))) (f)")

(assert-no-violations "hc-2 non-recursive immediate lambda: accepted"
  (check-source-termination "((lambda (x) (+ x 1)) 2)"))

(assert-true "hc-2 calling a value 0CFA cannot follow: unresolved-call"
  (exists (lambda (v) (eq? (termination-violation-kind v) 'unresolved-call))
          (check-source-termination "(define (f x) ((tool-get x f))) (f 1)")))

;; Step 6 (size-change termination): shapes the per-edge rule cannot prove.

(assert-no-violations "hc-2 sct: tree-sum through user-written my-map: accepted"
  (check-source-termination
    "(define (my-map g l) (if (null? l) '() (cons (g (car l)) (my-map g (cdr l))))) (define (tree-sum t) (if (pair? t) (apply + (my-map tree-sum t)) t))"))

;; Numeric descent is trusted only in place (round 5 C3), so a numeric
;; swap stays rejected, as on master. A structural swap is accepted.
(assert-rejected "hc-2 sct: numeric argument swap: rejected, as on master"
  "(define (f x y) (if (<= x 0) 0 (f y (- x 1))))")
(assert-no-violations "hc-2 sct: structural argument swap, both shrink every two calls: accepted"
  (check-source-termination "(define (f x y) (if (null? x) 0 (f y (cdr x))))"))

(assert-no-violations "hc-2 sct: tree recursion on car and cdr: accepted"
  (check-source-termination
    "(define (leaves t) (if (not (pair? t)) 1 (+ (leaves (car t)) (leaves (cdr t)))))"))

(assert-rejected "hc-2 sct: car of a non-decreasing argument: rejected"
  "(define (f t) (if (pair? t) (f (car (cons t t))) 1))")

(assert-rejected "hc-2 sct: argument swap with growth: rejected"
  "(define (f x y) (if (<= x 0) 0 (f (+ y 1) (- x 1))))")

;; A 7-cycle and a transposition generate all 5,040 permutations of the
;; formals, so the closure passes the 1,000-graph cap and fails closed.
(assert-true "hc-2 sct: closure over the cap: size-change-limit"
  (exists (lambda (v) (eq? (termination-violation-kind v) 'size-change-limit))
          (check-source-termination
            "(define (f a b c d e g h) (if (<= a 0) 0 (if (<= b 0) (f b c d e g h a) (f b a c d e g h))))")))

;; PR #729 review: false-accepts at f05b0b1, one must-reject case per repro.

;; C1: built-ins reached through apply, a HOF or call-with-values.
(assert-rejected "hc-2 c1: apply map: rejected"
  "(define (f x) (apply map (list f (list x)))) (f 1)")
(assert-rejected "hc-2 c1: apply apply: rejected"
  "(define (f x) (apply apply (list f (list x)))) (f 1)")
(assert-rejected "hc-2 c1: map apply: rejected"
  "(define (f x) (map apply (list f) (list (list x)))) (f 1)")
(assert-rejected "hc-2 c1: call-with-values into apply: rejected"
  "(define (f x) (call-with-values (lambda () (values f (list x))) apply)) (f 1)")
(assert-rejected "hc-2 c1: apply vector-set! then call the slot: rejected"
  "(define (f x) (let ((v (make-vector 1 0))) (apply vector-set! (list v 0 f)) ((vector-ref v 0) x))) (f 1)")
(assert-rejected "hc-2 c1: for-each vector-set! then call the slot: rejected"
  "(define (f x) (let ((v (make-vector 1 0))) (for-each vector-set! (list v) (list 0) (list f)) ((vector-ref v 0) x))) (f 1)")

;; C2: a call into a top-level case-lambda clause.
(assert-rejected "hc-2 c2: top-level case-lambda argument calls back: rejected"
  "(define (f g) (g g)) (f (case-lambda ((x) (f x))))")
(assert-no-violations "hc-2 c2: top-level case-lambda leaf argument: accepted"
  (check-source-termination "(define (f g) (g 1)) (f (case-lambda ((x) (+ x 1))))"))

;; C3: an anonymous cycle that swaps a shrinking and a growing argument.
(assert-rejected "hc-2 c3: anonymous self-application with argument swap: rejected"
  "(define (h l) (let ((self (lambda (s x y) (if (null? x) 0 (s s (cons 1 y) (cdr x)))))) (self self l l))) (h (list 1))")
(assert-rejected "hc-2 c3: anonymous self-application, car of a shadowed formal: rejected"
  "(define (h l) (let ((self (lambda (s x) (if (null? x) 0 (let ((x (list x))) (s s (car x))))))) (self self l))) (h (list 1))")
(assert-no-violations "hc-2 c3: anonymous self-application on cdr: accepted"
  (check-source-termination "(define (h l) (let ((self (lambda (s x) (if (null? x) 0 (s s (cdr x)))))) (self self l))) (h (list 1))"))

;; C4: a HOF bound to a name that shadows a different HOF.
(assert-rejected "hc-2 c4: fold-left bound to the name map: rejected"
  "(define (g acc e) (if (null? acc) 0 (f acc))) (define (f x) (let ((map fold-left)) (map g x (list 1)))) (f (list 1))")

;; C5: car and element arcs under a shadowing let.
(assert-rejected "hc-2 c5: car of a shadowed formal: rejected"
  "(define (f x) (if (null? x) 0 (let ((x (list x))) (f (car x))))) (f (list 1))")
(assert-rejected "hc-2 c5: for-each over a shadowed formal: rejected"
  "(define (f x) (if (null? x) 0 (let ((x (list x))) (for-each f x)))) (f (list 1))")

;; C6: case-lambda and rest-argument definitions.
(assert-rejected "hc-2 c6: case-lambda define calls itself through an alias: rejected"
  "(define f (case-lambda ((x) (let ((g f)) (g x))))) (f 1)")
(assert-rejected "hc-2 c6: letrec case-lambda calls itself through an alias: rejected"
  "(define (h) (letrec ((f (case-lambda ((x) (let ((g f)) (g x)))))) (f 1))) (h)")
(assert-rejected "hc-2 c6: rest-argument define applies itself: rejected"
  "(define f (lambda args (apply f args))) (f 1)")

;; K1: a call-with-values consumer gets the producer's values, not the
;; site's own arguments.
(assert-rejected "hc-2 k1: call-with-values consumer is the caller: rejected"
  "(define (th) (cons 1 th)) (define (loop x) (if (null? x) 0 (call-with-values (cdr x) loop))) (loop (th))")
(assert-rejected "hc-2 k1: call-with-values as a for-each callback: rejected"
  "(define (th) (cons 1 th)) (define (loop x) (if (null? x) 0 (for-each call-with-values (cdr x) (list loop)))) (loop (th))")

;; K2: apply reached through a HOF or another apply is not (apply f a ... lst)
;; at this site.
(assert-rejected "hc-2 k2: apply as a map callback: rejected"
  "(define (loop x) (if (null? x) 0 (begin (map apply (cdr x) (list (list x))) 0))) (loop (list 0 loop))")
(assert-rejected "hc-2 k2: apply applied to apply: rejected"
  "(define (loop x) (if (null? x) 0 (apply apply (car x) (list (list x))))) (loop (list loop))")

;; K3: named lets inside a definition still carry anonymous cycles and
;; aliased self-calls.
(assert-rejected "hc-2 k3: self-application inside named lets: rejected"
  "(define (f) ((lambda (x) (let lp () (x x))) (lambda (x) (let lp () (x x))))) (f)")
(assert-rejected "hc-2 k3: named let calls itself through an alias: rejected"
  "(define (g) (let loop ((n 10)) (if (= n 0) 0 (begin (loop (- n 1)) (let ((h loop)) (h n)))))) (g)")

;; K4: a closure built in one activation and called from a later one.
(assert-rejected "hc-2 k4: closure re-enters with a later activation's argument: rejected"
  "(define (f x k) (cond ((null? x) 0) (k (k k)) (else (f (cdr x) (lambda (self) (f (cdr x) self)))))) (f (list 1 2 3) #f)")

;; I1: a pair? guard is a base case for recursion through a built-in HOF.
(assert-no-violations "hc-2 i1: tree-sum under a pair? guard via map: accepted"
  (check-source-termination "(define (tree-sum t) (if (pair? t) (apply + (map tree-sum t)) t)) (tree-sum (list 1 (list 2 3)))"))
(assert-no-violations "hc-2 i1: depth under a pair? guard via map: accepted"
  (check-source-termination "(define (depth t) (if (pair? t) (+ 1 (apply max 0 (map depth t))) 0)) (depth (list 1 (list 2)))"))

;; Round 3 C1: a cond clause is not an application, so a lambda in it
;; escapes whatever its first element is.
(assert-rejected "hc-2 r3c1: lambda after map in a cond clause: rejected"
  "(define (f x k) (cond ((null? x) 0) (k (k k)) (else (f (cdr x) (cond (map (lambda (self) (f (cdr x) self)))))))) (f (list 1 2 3) #f)")
(assert-rejected "hc-2 r3c1: lambda as a cond clause test: rejected"
  "(define (f x k) (cond ((null? x) 0) (k (k k)) (else (f (cdr x) (cond ((lambda (self) (f (cdr x) self)))))))) (f (list 1 2 3) #f)")

;; Round 3 C2: a named-let call inside a closure belongs to a later
;; iteration.
(assert-rejected "hc-2 r3c2: named-let closure re-enters with an earlier n: rejected"
  "(define (g) (let lp ((n 10) (k #f)) (cond ((= n 0) 0) (k (k k)) (else (lp (- n 1) (lambda (self) (lp (- n 1) self))))))) (g)")

;; Round 3 C3: a top-level define named like a built-in HOF is not it.
(assert-rejected "hc-2 r3c3: named-let variable named map: rejected"
  "(define (g) (let lp ((n 10) (k #f) (map (lambda (h l) h))) (cond ((= n 0) 0) (k (k k)) (else (lp (- n 1) (map (lambda (self) (lp (- n 1) self)) (list 1)) map))))) (g)")
(assert-rejected "hc-2 r3c3: formal named map: rejected"
  "(define (f x k map) (cond ((null? x) 0) (k (k k)) (else (f (cdr x) (map (lambda (self) (f (cdr x) self map)) x) map)))) (f (list 1 2 3) #f (lambda (h l) h))")
(assert-rejected "hc-2 r3c3: user map returns its callback: rejected"
  "(define (map g l) g) (define (f x k) (cond ((null? x) 0) (k (k k)) (else (f (cdr x) (map (lambda (self) (f (cdr x) self)) x))))) (f (list 1 2 3) #f)")

;; Round 3 I1: a let-bound helper called in place runs in this activation.
(assert-no-violations "hc-2 r3i1: let-bound helper called in place: accepted"
  (check-source-termination "(define (f x) (let ((g (lambda () (f (cdr x))))) (if (null? x) 0 (g)))) (f (list 1 2))"))
(assert-rejected "hc-2 r3i1: let-bound helper that escapes: rejected"
  "(define (f x k) (let ((g (lambda (self) (f (cdr x) self)))) (cond ((null? x) 0) (k (k k)) (else (f (cdr x) g))))) (f (list 1 2 3) #f)")

;; Round 4 C1: a HOF name bound around the definition is not the built-in.
(assert-rejected "hc-2 r4c1: map bound by an enclosing let, mutual recursion: rejected"
  "(define (outer) (let ((map (lambda (h l) h))) (define (f x k) (if (null? x) 0 (if k (k k) (g (cdr x) (map (lambda (self) (g (cdr x) self)) x))))) (define (g x k) (f x k)) (f (list 1 2 3) #f))) (outer)")
(assert-rejected "hc-2 r4c1: map as a sibling internal define: rejected"
  "(define (outer) (define (map g l) g) (define (f x k) (if (null? x) 0 (if k (k k) (f (cdr x) (map (lambda (self) (f (cdr x) self)) x))))) (f (list 1 2 3) #f)) (outer)")
(assert-rejected "hc-2 r4c1: map as an enclosing lambda formal: rejected"
  "((lambda (map) (define (f x k) (if (null? x) 0 (if k (k k) (f (cdr x) (map (lambda (self) (f (cdr x) self)) x))))) (f (list 1 2 3) #f)) (lambda (h l) h))")

;; Round 4 C2: a wrapped lambda in operator position is still a definition.
(assert-rejected "hc-2 r4c2: eta-expanded omega at top level: rejected"
  "(((lambda (s) (lambda (n) ((s s) n))) (lambda (s) (lambda (n) ((s s) n)))) 1)")
(assert-rejected "hc-2 r4c2: Y combinator: rejected"
  "(define (Y f) ((lambda (x) (f (lambda (v) ((x x) v)))) (lambda (x) (f (lambda (v) ((x x) v)))))) ((Y (lambda (self) (lambda (n) (self n)))) 1)")
(assert-rejected "hc-2 r4c2: eta-omega through a define: rejected"
  "(define (app f) (f f)) ((app (lambda (s) (lambda (n) ((s s) n)))) 1)")
(assert-rejected "hc-2 r4c2: letrec loop in operator position: rejected"
  "((letrec ((lp (lambda (n) (lp n)))) lp) 1)")
(assert-rejected "hc-2 r4c2: letrec loop in a letrec non-lambda init: rejected"
  "(letrec ((v (list ((letrec ((lp (lambda (n) (lp n)))) lp) 1)))) v)")

;; Round 5 C1/C2: append keeps every procedure it is given.
(assert-rejected "hc-2 r5c1: procedure in apply append's spread: rejected"
  "(define (f x) ((apply append (list '() f)) x)) (f 1)")
(assert-rejected "hc-2 r5c1: procedure reaching append via call-with-values: rejected"
  "(define (f x) ((call-with-values (lambda () (values (list) f)) append) x)) (f 1)")
(assert-rejected "hc-2 r5c2: procedure in an improper append tail: rejected"
  "(define (f x) ((cdr (append (list 1) f)) x)) (f 1)")

;; Round 5 C3: numeric descent is trusted only in its own position.
(assert-rejected "hc-2 r5c3: arg swap with (- x 1) under (<= x 0): rejected"
  "(define (f x y) (if (<= x 0) 0 (f y (- x 1)))) (f 5 5)")
(assert-no-violations "hc-2 r5c3: even/odd numeric mutual recursion: accepted"
  (check-source-termination "(define (ev? n) (if (<= n 0) #t (od? (- n 1)))) (define (od? n) (if (<= n 0) #f (ev? (- n 1)))) (ev? 4)"))

;; Round 5 C4: a local binding is not the top-level one it shadows.
(assert-rejected "hc-2 r5c4: letrec helper shadowing a terminating top-level helper: rejected"
  "(define (helper n) (if (<= n 0) 0 (helper (- n 1)))) (define (f x) (letrec ((helper (lambda (g) (g g)))) (helper helper))) (f 1)")
(assert-rejected "hc-2 r5c4: internal define shadowing a terminating top-level helper: rejected"
  "(define (helper n) (if (<= n 0) 0 (helper (- n 1)))) (define (f x) (define (helper g) (g g)) (helper helper)) (f 1)")

;; The local binding keeps its own scope: rebinding stops the rename.
(assert-rejected "hc-2 r5c4: letrec* helper shadowing a terminating top-level helper: rejected"
  "(define (helper n) (if (<= n 0) 0 (helper (- n 1)))) (define (f x) (letrec* ((helper (lambda (g) (g g)))) (helper helper))) (f 1)")
(assert-rejected "hc-2 r5c4: two local helpers of one name, one loops: rejected"
  "(define (f x) (define (helper l) (if (null? l) 0 (helper (cdr l)))) (helper x)) (define (g y) (define (helper k) (k k)) (helper helper)) (f (list 1)) (g 1)")
(assert-no-violations "hc-2 r5c4: terminating local helper shadowing a top-level helper: accepted"
  (check-source-termination "(define (helper n) (if (<= n 0) 0 (helper (- n 1)))) (define (f x) (define (helper l) (if (null? l) 0 (helper (cdr l)))) (helper x)) (f (list 1 2))"))
(assert-no-violations "hc-2 r5c4: quoted and case-datum names are left alone: accepted"
  (check-source-termination "(define (helper n) (if (<= n 0) 0 (helper (- n 1)))) (define (f x) (define (helper l) (if (null? l) 0 (helper (cdr l)))) (case (car '(helper)) ((helper) (helper x)) (else 0))) (f (list 1 2))"))
;; Synthesized lambda@N node names cannot be captured by user definitions.
(assert-rejected "hc-2 r5c4: a user lambda@N definition does not hide an anonymous loop: rejected"
  "(define (lambda@2 n) (if (<= n 0) 0 (lambda@2 (- n 1)))) ((lambda (x) (x x)) (lambda (x) (x x)))")

;; Round 6 I1: a top-level redefinition rebinds the same variable.
(assert-rejected "hc-2 r6i1: card loop 2 behind a terminating definition of the same name: rejected"
  "(define (f n) (if (= n 0) 0 (f (- n 1)))) (define (f g) (g g)) (f f)")
(assert-rejected "hc-2 r6i1: redefinition by define of a lambda: rejected"
  "(define (f n) (if (= n 0) 0 (f (- n 1)))) (define f (lambda (g) (g g))) (f f)")
(assert-rejected "hc-2 r6i1: first-order redefinition inside a top-level begin: rejected"
  "(define (f n) (if (= n 0) 0 (f (- n 1)))) (begin (define (f n) (f n))) (f 1)")
(assert-rejected "hc-2 r6i1: set! of a top-level procedure to a loop: rejected"
  "(define (f n) (if (= n 0) 0 (f (- n 1)))) (set! f (lambda (g) (g g))) (f f)")

;; Round 5 I1: dynamic-wind thunks and cwv consumers run in this activation.
(assert-no-violations "hc-2 r5i1: recursion inside a dynamic-wind thunk: accepted"
  (check-source-termination "(define (f x) (if (null? x) 0 (dynamic-wind (lambda () 0) (lambda () (f (cdr x))) (lambda () 0)))) (f (list 1 2))"))
(assert-no-violations "hc-2 r5i1: recursion inside a call-with-values consumer: accepted"
  (check-source-termination "(define (f x) (if (null? x) 0 (call-with-values (lambda () (values 1 2)) (lambda (a b) (f (cdr x)))))) (f (list 1 2))"))
(assert-rejected "hc-2 r5i1: user dynamic-wind returns its thunk: rejected"
  "(define (dynamic-wind a b c) b) (define (f x k) (cond ((null? x) 0) (k (k k)) (else (f (cdr x) (dynamic-wind 0 (lambda (self) (f (cdr x) self)) 0))))) (f (list 1 2 3) #f)")

;; Round 7 C1/C2: a top-level definition of a builtin's name, or of the
;; synthesized element marker, is not the operator the checker trusts.
(assert-rejected "hc-2 r7c1: top-level %cfa-element identity: rejected"
  "(define (%cfa-element x) x) (define (f x) (if (null? x) 0 (f (%cfa-element x)))) (f (list 1))")
(assert-rejected "hc-2 r7c2: top-level car identity: rejected"
  "(define (car x) x) (define (f x) (if (null? x) 0 (f (car x)))) (f (list 1))")
(assert-rejected "hc-2 r7c2: top-level car as define of a lambda: rejected"
  "(define car (lambda (y) y)) (define (f x) (if (null? x) 0 (f (car x)))) (f (list 1))")
(assert-rejected "hc-2 r7c2: top-level cdr identity (pre-existing): rejected"
  "(define (cdr x) x) (define (f x) (if (null? x) 0 (f (cdr x)))) (f (list 1))")
(assert-rejected "hc-2 r7c2: top-level - returning its first argument (pre-existing): rejected"
  "(define (- a b) a) (define (f x) (if (= x 0) 0 (f (- x 1)))) (f 5)")
(assert-no-violations "hc-2 r7c2: a user my-car over the builtin car: accepted"
  (check-source-termination "(define (my-car p) (car p)) (define (f x) (if (null? x) 0 (f (cdr x)))) (f (list 1 2))"))

;; Round 7 C3: a formal that is set! in the body carries no size-change arc.
(assert-rejected "hc-2 r7c3: set! of the formal before (car x): rejected"
  "(define (f x) (if (null? x) 0 (begin (set! x (list x)) (f (car x))))) (f (list 1))")
(assert-rejected "hc-2 r7c3: set! of the formal before (cdr x) (pre-existing): rejected"
  "(define (f x) (if (null? x) 0 (begin (set! x (cons 1 x)) (f (cdr x))))) (f (list 1))")
(assert-rejected "hc-2 r7c3: set! of an anonymous lambda's formal: rejected"
  "((lambda (self x) (self self x)) (lambda (self x) (if (null? x) 0 (begin (set! x (cons 1 x)) (self self (cdr x))))) (list 1))")
(assert-no-violations "hc-2 r7c3: set! of a different local keeps the formal's arc: accepted"
  (check-source-termination "(define (f x) (let ((n 0)) (if (null? x) n (begin (set! n 1) (f (cdr x)))))) (f (list 1 2))"))

;; Round 8 C1: car or %cfa-element bound by an enclosing local binder is not descent.
(assert-rejected "hc-2 r8c1: enclosing let rebinds the descent operator: rejected"
  "(define (g) (let ((car (lambda (y) y))) (define (f x) (if (null? x) 0 (f (car x)))) (f (list 1)))) (g)")
(assert-rejected "hc-2 r8c1: enclosing let* rebinds the descent operator: rejected"
  "(define (g) (let* ((car (lambda (y) y))) (letrec ((f (lambda (x) (if (null? x) 0 (f (car x)))))) (f (list 1))))) (g)")
(assert-rejected "hc-2 r8c1: enclosing letrec rebinds the descent operator: rejected"
  "(define (g) (letrec ((car (lambda (y) y))) (define (f x) (if (null? x) 0 (f (car x)))) (f (list 1)))) (g)")
(assert-rejected "hc-2 r8c1: enclosing let-values rebinds the descent operator: rejected"
  "(define (g) (let-values (((car) (values (lambda (y) y)))) (define (f x) (if (null? x) 0 (f (car x)))) (f (list 1)))) (g)")
(assert-rejected "hc-2 r8c1: enclosing named-let variable rebinds the descent operator: rejected"
  "(define (g) (let lp ((car (lambda (y) y)) (i 0)) (define (f x) (if (null? x) 0 (f (car x)))) (f (list 1)))) (g)")
(assert-rejected "hc-2 r8c1: enclosing sibling internal define rebinds the descent operator: rejected"
  "(define (g) (define (car y) y) (define (f x) (if (null? x) 0 (f (car x)))) (f (list 1))) (g)")
(assert-rejected "hc-2 r8c1: enclosing do variable rebinds the descent operator: rejected"
  "(define (g) (do ((car (lambda (y) y) car) (i 0 (+ i 1))) ((= i 1) 0) (letrec ((f (lambda (x) (if (null? x) 0 (f (car x)))))) (f (list 1))))) (g)")
(assert-rejected "hc-2 r8c1: enclosing let, mutual recursion rebinds the descent operator: rejected"
  "(define (g) (let ((car (lambda (y) y))) (define (f x) (if (null? x) 0 (h x))) (define (h x) (f (car x))) (f (list 1)))) (g)")
(assert-rejected "hc-2 r8c1: enclosing let, %cfa-element rebinds the descent operator: rejected"
  "(define (g) (let ((%cfa-element (lambda (y) y))) (define (f x) (if (null? x) 0 (f (%cfa-element x)))) (f (list 1)))) (g)")
(assert-rejected "hc-2 r8c1: enclosing let, cdr (pre-existing) rebinds the descent operator: rejected"
  "(define (g) (let ((cdr (lambda (y) y))) (define (f x) (if (null? x) 0 (f (cdr x)))) (f (list 1)))) (g)")
(assert-no-violations "hc-2 r8c1: an enclosing let of an unrelated name keeps (cdr x) descent: accepted"
  (check-source-termination "(define (g) (let ((k 1)) (define (f x) (if (null? x) k (f (cdr x)))) (f (list 1 2)))) (g)"))
(assert-no-violations "hc-2 r8c1: a formal named list is renamed, descent on another formal still counts: accepted"
  (check-source-termination "(define (f list x) (if (null? x) list (f list (cdr x)))) (f 0 (list 1 2))"))

;; Round 9 C1: a local binder named after a syntactic keyword hides a call.
(assert-rejected "hc-2 r9c1: let-bound quote hides the real recursive call: rejected"
  "(define (f x y) (let ((quote (lambda (v) v))) (if (null? x) (quote (f x y)) (f y (cdr x))))) (f (list 1) (list 2))")
(assert-rejected "hc-2 r9c1: formal named quote hides the real recursive call: rejected"
  "(define (f x y quote) (if (null? x) (quote (f x y quote)) (f y (cdr x) quote))) (f (list 1) (list 2) (lambda (v) v))")
(assert-rejected "hc-2 r9c1: internal define named quote hides the real recursive call: rejected"
  "(define (f x y) (define (quote v) v) (if (null? x) (quote (f x y)) (f y (cdr x)))) (f (list 1) (list 2))")
(assert-rejected "hc-2 r9c1: let-bound if hides the real recursive call: rejected"
  "(define (f x) (let ((if (lambda (a b c) c))) (if (null? x) 0 (f x)))) (f (list 1))")

;; Round 9 I1's exemption (a HOF's empty list as base case) was deleted in
;; round 11 (C2): it also covered cycles that never passed through the HOF.
;; The delegating wrapper is a documented false rejection (README).
(assert-rejected "hc-2 r9i1: delegating for-each wrapper used nested: rejected (README limitation)"
  "(define (each l f) (for-each f l)) (each '((1 2) (3)) (lambda (r) (each r display)))")
(assert-rejected "hc-2 r9i1: a direct call beside the callback still needs a base case: rejected"
  "(define (each l f) (for-each f l) (each (cdr l) f)) (each '((1 2) (3)) (lambda (r) (each r display)))")
(assert-rejected "hc-2 r9i1: mutual recursion with no callback still needs a base case: rejected"
  "(define (f x) (g (cdr x))) (define (g x) (f (cdr x))) (f (list 1 2))")

;; Round 10 I1: an anonymous cycle still needs a base case.
(assert-rejected "hc-2 r10i1: self-application inside a define, no base case: rejected"
  "(define (f k) ((lambda (h) (h h k)) (lambda (self n) (self self (- n 1))))) (f 5)")
(assert-rejected "hc-2 r10i1: top-level case-lambda self-application, no base case: rejected"
  "(let ((cl (case-lambda ((s n) (s s (- n 1)))))) (cl cl 5))")
(assert-no-violations "hc-2 r10i1: anonymous self-application with a base case: accepted"
  (check-source-termination "(define (f k) ((lambda (h) (h h k)) (lambda (self n) (if (<= n 0) 0 (self self (- n 1)))))) (f 5)"))

;; Round 10 I2: parameterize calls its parameter.
(assert-rejected "hc-2 r10i2: parameterize hides a zero-argument call: rejected"
  "(define (f k) (parameterize ((k 1)) 0)) (define (k0) (f k0)) (f k0)")
(assert-rejected "hc-2 r10i2: parameterize calls its parameter with one argument: rejected"
  "(define (f k) (parameterize ((k 1)) 0)) (define (k1 x) (f k1)) (f k1)")
(assert-no-violations "hc-2 r10i2: parameterize over a non-recursive case-lambda: accepted"
  (check-source-termination "(define p (case-lambda (() 0) ((x) x))) (parameterize ((p 1)) (display 2))"))

;; Round 10 I3: apply calls its procedure once, so it is not a list-HOF callback.
(assert-rejected "hc-2 r10i3: apply through a global alias, no base case: rejected"
  "(define (g n z) (f n)) (define gg g) (define (f n) (apply gg (- n 1) (list 0))) (f 5)")
(assert-rejected "hc-2 r10i3: top-level %cfa-spread identity: rejected"
  "(define (%cfa-spread x) x) (define (f x) (if (null? x) 0 (f (%cfa-spread x)))) (f (list 1))")

;; Round 10 I4: a named let inside a top-level anonymous lambda.
(assert-no-violations "hc-2 r10i4: named let inside a top-level for-each lambda: accepted"
  (check-source-termination "(for-each (lambda (n) (let lp ((i n)) (when (> i 0) (display i) (lp (- i 1))))) (list 1 2 3))"))
(assert-no-violations "hc-2 r10i4: named let inside a let-bound lambda: accepted"
  (check-source-termination "(let ((count-down (lambda (n) (let lp ((i n) (acc '())) (if (<= i 0) acc (lp (- i 1) (cons i acc))))))) (display (count-down 5)))"))
(assert-no-violations "hc-2 r10i4: named let inside a map lambda in a top-level define: accepted"
  (check-source-termination "(define lst (map (lambda (x) (let lp ((k x) (acc 1)) (if (<= k 0) acc (lp (- k 1) (* acc k))))) (list 1 2 3))) (display lst)"))
(assert-no-violations "hc-2 r10i4: for-each lambda with a named let inside a top-level loop: accepted"
  (check-source-termination "(let loop ((i 0)) (when (< i 3) (for-each (lambda (j) (let inner ((k j)) (when (> k 0) (display k) (inner (- k 1))))) (list i)) (loop (+ i 1))))"))

(assert-rejected "hc-2 r10i4: named let in a top-level lambda calling back into its caller: rejected"
  "(define (k p) (p p)) (k (lambda (self) (let lp ((i 1)) (when (> i 0) (k self) (lp (- i 1))))))")

;; Round 10 I5: definitions in operator position or inside a wrapped lambda.
(assert-no-violations "hc-2 r10i5: letrec in operator position: accepted"
  (check-source-termination "(display ((letrec ((len (lambda (l) (if (null? l) 0 (+ 1 (len (cdr l))))))) len) (list 1 2 3)))"))
(assert-no-violations "hc-2 r10i5: internal define in an applied lambda with an argument: accepted"
  (check-source-termination "(display ((lambda (lst) (define (len l) (if (null? l) 0 (+ 1 (len (cdr l))))) (len lst)) (list 1 2 3)))"))
(assert-no-violations "hc-2 r10i5: internal define in an applied thunk: accepted"
  (check-source-termination "((lambda () (define (helper n) (if (<= n 0) 0 (+ 1 (helper (- n 1))))) (display (helper 5))))"))

(assert-rejected "hc-2 r10i5: non-decreasing letrec in operator position: rejected"
  "(display ((letrec ((len (lambda (l) (if (null? l) 0 (+ 1 (len l)))))) len) (list 1 2 3)))")
(assert-rejected "hc-2 r10i5: non-decreasing internal define in an applied thunk: rejected"
  "((lambda () (define (helper n) (if (= n 0) 0 (+ 1 (helper (+ n 1))))) (display (helper 5))))")

;; Round 10 I6: a mutual base case must test a formal.
(assert-rejected "hc-2 r10i6: mutual numeric descent guarded only by string?: rejected"
  "(define (f x) (if (string? x) 0 (g x))) (define (g x) (f (- x 1))) (f 5)")
(assert-rejected "hc-2 r10i6: mutual numeric descent on both edges guarded only by string?: rejected"
  "(define (f x) (if (string? x) 0 (g (- x 1)))) (define (g x) (f (- x 1))) (f 5)")
(assert-no-violations "hc-2 r10i6: even/odd with a lower stop: accepted"
  (check-source-termination "(define (ev n) (if (<= n 0) #t (od (- n 1)))) (define (od n) (if (<= n 0) #f (ev (- n 1)))) (ev 4)"))
(assert-no-violations "hc-2 r10i6: mutual structural descent with a pair? test: accepted"
  (check-source-termination "(define (f x) (if (pair? x) (g (cdr x)) 0)) (define (g x) (f x)) (f (list 1 2))"))

;; Round 10 minor: a multi-operand - or + is not a unit step.
(assert-rejected "hc-2 r10m: (- x 1 -5) is not descent: rejected"
  "(define (f x) (if (<= x 0) 0 (f (- x 1 -5)))) (f 3)")
(assert-rejected "hc-2 r10m: (+ x 1 -5) is not an increase: rejected"
  "(define (f x) (if (>= x 10) 0 (f (+ x 1 -5)))) (f 3)")
(assert-no-violations "hc-2 r10m: (- x 1) is still descent: accepted"
  (check-source-termination "(define (f x) (if (<= x 0) 0 (f (- x 1)))) (f 3)"))

;; Round 11 C1: an empty spread set is still a spread, so a nested
;; apply's site arguments are not its procedure's arguments.
(assert-rejected "hc-2 r11c1: apply of apply with an all-data list: rejected"
  "(define (g a b) (if (null? b) 0 (apply apply g (cdr b) (cons 1 b) (list '())))) (g 0 (list 1))")

;; Round 11 C2: a member that only calls back through a HOF is no base
;; case for a cycle that never passes through it.
(assert-rejected "hc-2 r11c2: numeric self-loop beside a for-each callback edge: rejected"
  "(define (f l k) (for-each k l)) (define (g x) (if (pair? x) (f x g) (g (- x 1)))) (f (list 5) g)")
(assert-rejected "hc-2 r11c2: numeric g/h loop beside a for-each callback edge: rejected"
  "(define (f l k) (for-each k l)) (define (g x) (if (pair? x) (f x g) (h (- x 1)))) (define (h y) (g (- y 1))) (f (list 5) g)")

;; Round 11 C3: every cycle must pass through a member with its own base case.
(assert-rejected "hc-2 r11c3: callee's base case does not cover the caller's self-loop: rejected"
  "(define (f l k) (if (null? l) 0 (k (car l)))) (define (g x) (if (pair? x) (f x g) (g (- x 1)))) (f (list 5) g)")
(assert-rejected "hc-2 r11c3: named mutual recursion, g loops without a base case: rejected"
  "(define (f n) (if (= n 0) 0 (g (- n 1)))) (define (g n) (if (> n 100) (f (- n 1)) (g (- n 1)))) (f 5)")
(assert-rejected "hc-2 r11c3: set!-bound lambdas, g loops without a base case: rejected"
  "(define (run a) (let ((f #f) (g #f)) (set! f (lambda (n) (if (= n 0) 0 (g (- n 1))))) (set! g (lambda (n) (if (> n 100) (f (- n 1)) (g (- n 1))))) (f a))) (run 5)")
(assert-no-violations "hc-2 r11c3: every cycle passes a base-case member: accepted"
  (check-source-termination "(define (f n) (if (<= n 0) 0 (g (- n 1)))) (define (g n) (if (<= n 0) 1 (if (odd? n) (f (- n 1)) (g (- n 1))))) (f 5)"))

;; Round 11 I1: quoted data, dotted or not, is never walked as code.
(assert-no-violations "hc-2 r11i1: assoc on a quoted alist inside a for-each lambda: accepted"
  (check-source-termination "(define (process-all items) (for-each (lambda (item) (let ((r (assoc item '((a . 1) (b . 2))))) (when r (display (cdr r))))) items)) (process-all '(a b))"))
(assert-no-violations "hc-2 r11i1: assoc on a quoted alist in a let binding: accepted"
  (check-source-termination "(define (lookup k) (let ((r (assoc k '((a . 1) (b . 2))))) (if r (cdr r) 0))) (display (map lookup '(a b)))"))
(assert-no-violations "hc-2 r11i1: quoted alist as a direct argument: accepted"
  (check-source-termination "(define (lookup k) (assoc k '((a . 1) (b . 2)))) (display (lookup 'a))"))
(assert-no-violations "hc-2 r11i1: quoted dotted pair at top level: accepted"
  (check-source-termination "(define x '(1 . 2)) (define (f l) (if (null? l) 0 (+ 1 (f (cdr l))))) (display (f (list (car x))))"))

;; Round 12 C1: numeric descent on one edge does not carry a mutual
;; cycle through an edge that decreases nothing (master's per-edge rule).
(assert-rejected "hc-2 r12c1: (> n 10) test, g passes n through unchanged: rejected"
  "(define (f n) (if (> n 10) 0 (g n))) (define (g n) (f (- n 1))) (f 5)")
(assert-rejected "hc-2 r12c1: step of 2 over (= n 0), f passes n through: rejected"
  "(define (f n) (if (= n 0) 0 (g n))) (define (g n) (f (- n 2))) (f 5)")
(assert-rejected "hc-2 r12c1: base case on l while n descends on one edge: rejected"
  "(define (f n l) (if (null? l) 0 (g n))) (define (g n) (f (- n 1) (list 1))) (f 5 (list 1))")
(assert-rejected "hc-2 r12c1: descent inside an in-place let-bound closure, g passes n through: rejected"
  "(define (f n) (let ((k (lambda () (g (- n 1))))) (if (= n 0) (k) (k)))) (define (g n) (f n)) (f 5)")
(assert-no-violations "hc-2 r12c1: mutual structural walk with a pass-through edge: accepted"
  (check-source-termination "(define (walk-tree t) (if (pair? t) (walk-list t) 1)) (define (walk-list l) (if (null? l) 0 (+ (walk-tree (car l)) (walk-list (cdr l))))) (display (walk-tree '(1 (2 3) 4)))"))

;; Round 13 I1: the round-12 rule holds for anonymous cycles too, here
;; set!-bound and self-passing lambdas inside a define.
(assert-rejected "hc-2 r13i1: set!-bound lambdas, (> n 10) test, b passes n through: rejected"
  "(define (run) (let ((a #f) (b #f)) (set! a (lambda (n) (if (> n 10) 0 (b n)))) (set! b (lambda (n) (a (- n 1)))) (a 5))) (run)")
(assert-rejected "hc-2 r13i1: set!-bound lambdas, step of 2 over (= n 0): rejected"
  "(define (run) (let ((a #f) (b #f)) (set! a (lambda (n) (if (= n 0) 0 (b n)))) (set! b (lambda (n) (a (- n 2)))) (a 5))) (run)")
(assert-rejected "hc-2 r13i1: set!-bound lambdas, base case on l while n descends on one edge: rejected"
  "(define (run) (let ((a #f) (b #f)) (set! a (lambda (n l) (if (null? l) 0 (b n)))) (set! b (lambda (n) (a (- n 1) (list 1)))) (a 5 (list 1)))) (run)")
(assert-rejected "hc-2 r13i1: self-passing lambdas, (> n 10) test, a passes n through: rejected"
  "(define (run) (let ((a (lambda (self other n) (if (> n 10) 0 (other other self n)))) (b (lambda (self other n) (other other self (- n 1))))) (a a b 5))) (run)")
(assert-no-violations "hc-2 r13i1: set!-bound mutual structural walk with a pass-through edge: accepted"
  (check-source-termination "(define (run t) (let ((wt #f) (wl #f)) (set! wt (lambda (t) (if (pair? t) (wl t) 1))) (set! wl (lambda (l) (if (null? l) 0 (+ (wt (car l)) (wl (cdr l)))))) (wt t))) (display (run '(1 (2 3) 4)))"))

;; Round 14 I1: the guard variable is bound in the 0CFA; a call through
;; it after set! is a call the analysis cannot resolve.
(assert-rejected "hc-2 r14i1: (set! e loop) inside a guard clause, then (e n): rejected"
  "(define (loop n) (guard (e (#t (set! e loop) (e n))) (car '()))) (loop 1)")
(assert-rejected "hc-2 r14i1: (set! e f) inside a top-level guard clause, then (e e): rejected"
  "(define (f g) (g g)) (guard (e (#t (set! e f) (e e))) (car '()))")
(assert-rejected "hc-2 r14i1: a raised procedure called from the guard clause: rejected"
  "(define (loop n) (guard (e (#t (e n))) (raise loop))) (loop 1)")
(assert-no-violations "hc-2 r14i1: guard with a constant fallback: accepted"
  (check-source-termination "(define (safe-car l) (guard (e (#t 0)) (car l))) (display (safe-car '()))"))
(assert-no-violations "hc-2 r14i1: structural recursion inside a guard body: accepted"
  (check-source-termination "(define (len l) (guard (e (#t 0)) (if (null? l) 0 (+ 1 (len (cdr l)))))) (display (len '(1 2)))"))

;; Round 14 minor: a cyclic quoted literal must not hang the checker.
(assert-rejected "hc-2 r14m: cyclic quoted literal, (f (car x)): rejected without hanging"
  "(define (f x) (if (pair? x) (f (car x)) 0)) (f '#0=(#0#))")
(assert-rejected "hc-2 r14m: cyclic quoted list, (f (cdr l)): rejected"
  "(define (f l) (if (pair? l) (f (cdr l)) 0)) (f '#0=(1 . #0#))")
(assert-rejected "hc-2 r14m: cyclic quoted vector walked by vector-ref: rejected"
  "(define (f v) (if (vector? v) (f (vector-ref v 0)) 0)) (f '#0=#(#0#))")
(assert-rejected "hc-2 r14m: cyclic code form: rejected without hanging"
  "(define (f x) #0=(+ 1 #0#))")
(assert-no-violations "hc-2 r14m: shared acyclic datum label: accepted"
  (check-source-termination "(define (f l) (if (pair? l) (f (cdr l)) 0)) (display (f '(#0=(1 2) #0#)))"))

;; Round 15 C1/C2: the "bound minus x" measure holds only for a formal
;; an upper-bound test constrains, with a bound that cannot grow: every
;; formal it mentions passes unchanged in place, its operators are pure
;; size functions, and nothing it names is assigned.
(assert-rejected "hc-2 r15c1: bound arcs on an unconstrained formal n: rejected"
  "(define (f i n l) (if (>= i 10) 0 (if (null? l) (f i (+ n 1) (list 1)) (f i n (cdr l))))) (f 0 0 '())")
(assert-rejected "hc-2 r15c2: bound (length l) while l grows: rejected"
  "(define (f i l m) (if (>= i (length l)) 0 (if (null? m) (f (+ i 1) l (cons 1 m)) (f i (cons 1 (cons 1 l)) (cdr m))))) (f 0 (list 1) (list 1))")
(assert-rejected "hc-2 r15i1: i passed through, only n grows: rejected"
  "(define (f i n) (if (>= i 10) 0 (f i (+ n 1)))) (f 0 0)")
(assert-rejected "hc-2 r15i1: bound (* 2 n) grows with i: rejected"
  "(define (f i n) (if (>= i (* 2 n)) 0 (f (+ i 1) (+ n 1)))) (f 0 5)")
(assert-rejected "hc-2 r15i1: bound (vector-length v) while v grows: rejected"
  "(define (f i v) (if (>= i (vector-length v)) 0 (f (+ i 1) (make-vector (+ 2 (vector-length v)) 0)))) (f 0 (vector 1))")
(assert-rejected "hc-2 r15i1: bound (length l) while l grows each call: rejected"
  "(define (f i l) (if (>= i (length l)) 0 (f (+ i 1) (cons 1 (cons 1 l))))) (f 0 (list 1))")
(assert-rejected "hc-2 r15: bound is a global the body raises: rejected"
  "(define lim 10) (define (f i) (if (>= i lim) 0 (begin (set! lim (+ lim 2)) (f (+ i 1))))) (f 0)")
(assert-rejected "hc-2 r15: bound read through a user function: rejected"
  "(define c 0) (define (lim) (set! c (+ c 2)) c) (define (f i) (if (>= i (lim)) 0 (f (+ i 1)))) (f 0)")
(assert-rejected "hc-2 r15: when runs its body when the upper-bound test holds: rejected"
  "(define (f i) (when (>= i 10) (f (+ i 1)))) (f 10)")
(assert-no-violations "hc-2 r15: index up to (vector-length v), v passed in place: accepted"
  (check-source-termination "(define (f i v) (if (>= i (vector-length v)) 0 (+ (vector-ref v i) (f (+ i 1) v)))) (display (f 0 (vector 1 2)))"))
(assert-no-violations "hc-2 r15: index up to a literal, accumulator grows: accepted"
  (check-source-termination "(define (f i acc) (if (>= i 10) acc (f (+ i 1) (cons i acc)))) (display (f 0 '()))"))
(assert-no-violations "hc-2 r15: index up to (- (length l) 1), l in place: accepted"
  (check-source-termination "(define (f i l) (if (>= i (- (length l) 1)) 0 (f (+ i 1) l))) (display (f 0 '(1 2 3)))"))
(assert-no-violations "hc-2 r15: unless with an upper-bound test: accepted"
  (check-source-termination "(define (f i) (unless (>= i 10) (f (+ i 1)))) (f 0)"))

;; HC-3: dotted formals crashed check-termination ("not a proper list").
(define (check-source-termination/no-crash source)
  (guard (e (#t (list 'crash)))
    (check-source-termination source)))
(assert-no-violations "hc-3 rest args, non-recursive: accepted"
  (check-source-termination/no-crash "(define (f . args) (length args)) (display (f 1 2))"))
(assert-no-violations "hc-3 required plus rest args, non-recursive: accepted"
  (check-source-termination/no-crash "(define (f a . rest) (cons a rest)) (display (f 1 2))"))
(assert-no-violations "hc-3 dotted lambda formals: accepted"
  (check-source-termination/no-crash "(define g (lambda (a . r) a)) (display ((lambda (x . y) (g x)) 1 2))"))
(assert-true "hc-3 rest args through apply loops: rejected"
  (let ((v (check-source-termination/no-crash "(define (f . args) (apply f args)) (f 1)")))
    (and (pair? v) (not (equal? v (list (quote crash)))))))
(assert-true "hc-3 rest args, direct self call loops: rejected"
  (let ((v (check-source-termination/no-crash "(define (f a . rest) (f a)) (f 1)")))
    (and (pair? v) (not (equal? v (list (quote crash)))))))
(assert-true "hc-3 internal define with rest args: no crash"
  (list? (guard (e (#t #f)) (check-source-termination "(define (g n) (define (h a . r) (if (<= a 0) 0 (h (- a 1)))) (h n)) (display (g 3))"))))
(assert-true "hc-3 letrec lambda with rest args: no crash"
  (list? (guard (e (#t #f)) (check-source-termination "(define (g n) (letrec ((h (lambda (a . r) (if (<= a 0) 0 (h (- a 1)))))) (h n))) (display (g 3))"))))
(assert-no-violations "hc-3 do loop inside a rest-args function: accepted"
  (check-source-termination/no-crash "(define (g . r) (do ((i 0 (+ i 1))) ((>= i 3) r))) (display (g 1))"))
(assert-true "hc-3 rest param shadows the measured formal: rejected"
  (let ((v (check-source-termination/no-crash "(define (f x) (if (null? x) 0 ((lambda (a . x) (f (cdr x))) 1 x x))) (f '(1))")))
    (and (pair? v) (not (equal? v (list (quote crash)))))))
(assert-no-violations "hc-3 rest-args lambda whose first formal names a user HOF: accepted"
  (check-source-termination/no-crash "(define (app h x) (h x)) (define (k a) ((lambda (app . s) app) 1 2)) (display (k 1))"))

;; HC-4: false accepts found by the HC-2 round-16 review (PR #729).
;; I1: a bound read through a body-local binding may grow between calls.
(assert-rejected "hc-4 i1: bound n let-bound from a growing l: rejected"
  "(define (f i l) (let ((n (length l))) (if (>= i n) 0 (f (+ i 1) (cons 1 l))))) (display (f 0 '(1 2)))")
(assert-rejected "hc-4 i1: bound n from an internal define: rejected"
  "(define (f i l) (define n (length l)) (if (>= i n) 0 (f (+ i 1) (cons 1 l)))) (display (f 0 '(1 2)))")
(assert-rejected "hc-4 i1: bound n from let* over a rebound l: rejected"
  "(define (f i l) (let* ((l (cons 1 l)) (n (length l))) (if (>= i n) 0 (f (+ i 1) l)))) (display (f 0 '(1 2)))")
(assert-no-violations "hc-4 i1: bound is a top-level constant: accepted"
  (check-source-termination "(define n 10) (define (f i) (if (>= i n) 0 (f (+ i 1)))) (display (f 0))"))
;; I3: a base case must guard the recursive call it is credited for.
(assert-rejected "hc-4 i3: upper-bound test in a separate statement: rejected"
  "(define (f i) (if (>= i 10) 0 0) (f (+ i 1))) (display (f 0))")
(assert-rejected "hc-4 i3: one branch recurses with no bound test: rejected"
  "(define (f i j) (if (> j 0) (if (>= i 10) 0 (f (+ i 1) j)) (f (+ i 1) j))) (display (f 0 0))")
(assert-rejected "hc-4 i3: lower stop in a separate statement: rejected"
  "(define (f n) (if (<= n 0) 0 0) (f (- n 1))) (display (f 3))")
(assert-no-violations "hc-4 i3: countdown guarded by its lower stop: accepted"
  (check-source-termination "(define (f n) (if (<= n 0) 0 (f (- n 1)))) (display (f 3))"))
(assert-no-violations "hc-4 i3: count-up guarded by unless: accepted"
  (check-source-termination "(define (f i) (unless (>= i 10) (f (+ i 1)))) (f 0)"))
(assert-no-violations "hc-4 i3: countdown guarded by when (> n 0): accepted"
  (check-source-termination "(define (f n) (when (> n 0) (f (- n 1)))) (f 3)"))
(assert-no-violations "hc-4 i3: countdown in a cond else clause: accepted"
  (check-source-termination "(define (f n) (cond ((<= n 0) 0) (else (f (- n 1))))) (display (f 3))"))
;; I4: a base case on one formal does not stop descent on another.
(assert-rejected "hc-4 i4: lower stop on m, descent on n: rejected"
  "(define (f n m) (if (<= m 0) 0 (f (- n 1) m))) (display (f 3 1))")
(assert-rejected "hc-4 i4: upper-bound test on n, descent on n: rejected"
  "(define (f n) (if (>= n 10) 0 (f (- n 1)))) (display (f 3))")

;; HC-4 review: a mutual guard against a formal crashed (cdr #f).
(assert-true "hc-4 mutual guard against a formal: no crash"
  (list? (guard (e (#t #f)) (check-source-termination "(define (ev n m) (if (= n 0) #t (if (< n m) #t (od (- n 1) m)))) (define (od n m) (if (= n 0) #f (ev (- n 1) m))) (display (ev 10 3))"))))
;; HC-4 review: the anonymous-lambda path trusted unguarded numeric arcs.
(assert-rejected "hc-4 anon i3: lower stop in a separate statement: rejected"
  "(define (k) ((lambda (s) (s s 3)) (lambda (self n) (if (<= n 0) 0 0) (self self (- n 1))))) (display (k))")
(assert-rejected "hc-4 anon i4: lower stop on m, descent on n: rejected"
  "(define (k) ((lambda (s) (s s 3 1)) (lambda (self n m) (if (<= m 0) 0 (self self (- n 1) m))))) (display (k))")
(assert-no-violations "hc-4 anon: guarded countdown: accepted"
  (check-source-termination "(define (k) ((lambda (s) (s s 3)) (lambda (self n) (if (<= n 0) 0 (self self (- n 1)))))) (display (k))"))

;; ============================================================
;; HC-5: a do-loop step must move a tested variable toward the exit test
;; ============================================================
(display "=== HC-5: do-loop step progress ===") (newline)

(assert-rejected "hc-5 step leaves the tested variable unchanged: rejected"
  "(define (g) (do ((i 0 i)) ((>= i 3) 0))) (display (g))")
(assert-rejected "hc-5 descent under an upper-bound exit test: rejected"
  "(do ((i 0 (- i 1))) ((>= i 3) 0))")
(assert-rejected "hc-5 ascent under a lower-bound exit test: rejected"
  "(do ((i 0 (+ i 1))) ((<= i -1) 0))")
(assert-rejected "hc-5 stepped variable is not the tested one: rejected"
  "(do ((i 0 (+ i 1)) (j 0 j)) ((>= j 3) 0))")
(assert-rejected "hc-5 bound is a stepped loop variable: rejected"
  "(do ((i 0 (+ i 1)) (n 3 (+ n 1))) ((>= i n) 0))")
(assert-rejected "hc-5 two stepped variables that can cross: rejected"
  "(do ((i 0 (+ i 1)) (j 11 (- j 1))) ((= i j) 0))")
(assert-rejected "hc-5 body resets the progress variable: rejected"
  "(do ((i 0 (+ i 1))) ((>= i 3) 0) (set! i 0))")
(assert-rejected "hc-5 bound assigned in the body: rejected"
  "(define n 3) (define (g) (do ((i 0 (+ i 1))) ((>= i n) 0) (set! n (+ n 1)))) (g)")
(assert-rejected "hc-5 bound is a user call: rejected"
  "(define (f) 3) (do ((i 0 (+ i 1))) ((>= i (f)) 0))")
(assert-rejected "hc-5 do-loop with no variables: rejected"
  "(define (g) (do () ((= 1 2) 0))) (g)")
(assert-rejected "hc-5 conjunction gives no stop: rejected"
  "(do ((i 0 (+ i 1))) ((and (>= i 3) (< i 0)) 0))")

(assert-no-violations "hc-5 count up to a literal: accepted"
  (check-source-termination "(do ((i 0 (+ i 1))) ((>= i 3) 0))"))
(assert-no-violations "hc-5 mirrored upper bound: accepted"
  (check-source-termination "(do ((i 0 (+ i 1))) ((<= 3 i) 0))"))
(assert-no-violations "hc-5 countdown to (<= n 0): accepted"
  (check-source-termination "(do ((n 10 (- n 1))) ((<= n 0) 0))"))
(assert-no-violations "hc-5 countdown under a negated pass test: accepted"
  (check-source-termination "(do ((n 10 (sub1 n))) ((not (> n 0)) 0))"))
(assert-no-violations "hc-5 mirrored lower bound: accepted"
  (check-source-termination "(do ((n 10 (- n 1))) ((>= 0 n) 0))"))
(assert-no-violations "hc-5 list walk: accepted"
  (check-source-termination "(do ((l '(1 2 3) (cdr l)) (s 0 (+ s (car l)))) ((null? l) s))"))
(assert-no-violations "hc-5 disjunction with one progressing test: accepted"
  (check-source-termination "(do ((i 0 (+ i 1)) (l '(1 2) (cdr l))) ((or (eq? l 'x) (>= i 10)) i))"))
(assert-no-violations "hc-5 vector-length bound: accepted"
  (check-source-termination "(define (g v) (do ((i 0 (+ i 1))) ((>= i (vector-length v)) 0))) (g (vector 1 2))"))
(assert-no-violations "hc-5 unstepped loop variable as bound: accepted"
  (check-source-termination "(do ((i 0 (+ i 1)) (n 5)) ((>= i n) i))"))
(assert-no-violations "hc-5 set! of an unrelated variable: accepted"
  (check-source-termination "(define (g) (let ((acc 0)) (do ((i 0 (+ i 1))) ((>= i 3) acc) (set! acc (+ acc i))))) (g)"))

;; ============================================================
;; HC-7: named let applies the bound and guard rules of Phases 5 and 6
;; ============================================================
(display "=== HC-7: named-let bound and guard rules ===") (newline)

(assert-rejected "hc-7 p9 bound (length l) grows under (cons 1 l): rejected"
  "(define (f lst) (let loop ((i 0) (l lst)) (if (>= i (length l)) 0 (loop (+ i 1) (cons 1 l)))))")
(assert-rejected "hc-7 p12 test in an earlier statement guards nothing: rejected"
  "(define (f) (let loop ((i 0)) (if (>= i 10) 0 0) (loop (+ i 1))))")
(assert-rejected "hc-7 ascent with no upper-bound test: rejected"
  "(define (f n) (let loop ((i 0)) (if (= n 0) 0 (loop (+ i 1)))))")
(assert-rejected "hc-7 descent tested in another branch: rejected"
  "(define (f n) (let loop ((k n)) (if (<= k 0) (loop (- k 1)) 0)))")
(assert-rejected "hc-7 bound assigned by set!: rejected"
  "(define (f n) (let loop ((i 0)) (if (>= i n) 0 (begin (set! n (+ n 1)) (loop (+ i 1))))))")
(assert-rejected "hc-7 loop variable reset by set!: rejected"
  "(define (f l) (let loop ((x l)) (if (null? x) 0 (begin (set! x l) (loop (cdr x))))))")
(assert-no-violations "hc-7 ascent to (vector-length v): accepted"
  (check-source-termination "(define (f v) (let loop ((i 0)) (if (>= i (vector-length v)) 0 (loop (+ i 1)))))"))
(assert-no-violations "hc-7 ascent with l passed in place: accepted"
  (check-source-termination "(define (f lst) (let loop ((i 0) (l lst)) (if (>= i (length l)) 0 (loop (+ i 1) l))))"))
(assert-no-violations "hc-7 countdown under (<= k 0): accepted"
  (check-source-termination "(define (f n) (let loop ((k n)) (if (<= k 0) 0 (loop (- k 1)))))"))
(assert-no-violations "hc-7 countdown under when: accepted"
  (check-source-termination "(define (f n) (let loop ((k n)) (when (> k 0) (loop (- k 1)))))"))
(assert-no-violations "hc-7 list walk with accumulator: accepted"
  (check-source-termination "(define (f x) (let loop ((l x) (acc 0)) (if (null? l) acc (loop (cdr l) (+ acc 1)))))"))
(assert-no-violations "hc-7 nested loops, inner bound is the outer variable: accepted"
  (check-source-termination "(define (f n) (let outer ((i 0)) (if (>= i n) 0 (let inner ((j 0)) (if (>= j i) (outer (+ i 1)) (inner (+ j 1)))))))"))

(assert-rejected "hc-7 when (< i (length l)) with l grown: rejected"
  "(define (f lst) (let loop ((i 0) (l lst)) (when (< i (length l)) (loop (+ i 1) (cons 1 l)))))")
(assert-rejected "hc-7 when (> i 10) holds above the bound: rejected"
  "(define (f) (let loop ((i 0)) (when (> i 10) (loop (+ i 1)))))")
(assert-rejected "hc-7 when (< i 10) with descent: rejected"
  "(define (f) (let loop ((i 0)) (when (< i 10) (loop (- i 1)))))")
(assert-rejected "hc-7 when (< j 10) guards a different variable: rejected"
  "(define (f j) (let loop ((i 0)) (when (< j 10) (loop (+ i 1)))))")
(assert-no-violations "hc-7 when (> 10 i): accepted"
  (check-source-termination "(define (f) (let loop ((i 0)) (when (> 10 i) (loop (+ i 1)))))"))
(assert-no-violations "hc-7 when (not (>= i 10)): accepted"
  (check-source-termination "(define (f) (let loop ((i 0)) (when (not (>= i 10)) (loop (+ i 1)))))"))
(assert-no-violations "hc-7 direct recursion under when (< i 10): accepted"
  (check-source-termination "(define (f i) (when (< i 10) (f (+ i 1))))"))
(assert-rejected "hc-7 direct recursion under when (< i (length l)), l grown: rejected"
  "(define (f i l) (when (< i (length l)) (f (+ i 1) (cons 1 l))))")

;; ============================================================
;; HC-6: (= n 0) and (zero? n) do not bound numeric descent from below
;; ============================================================
(display "=== HC-6: equality stops are not lower bounds ===") (newline)

;; (f -1) steps past 0 forever, so an equality stop proves no descent.
(assert-rejected "hc-6 (= x 0) countdown called with -1: rejected"
  "(define (f x) (if (= x 0) 0 (f (- x 1)))) (f -1)")
(assert-rejected "hc-6 (zero? x) countdown: rejected"
  "(define (f x) (if (zero? x) 0 (f (- x 1)))) (f 3)")
(assert-rejected "hc-6 factorial under (= n 0): rejected"
  "(define (factorial n) (if (= n 0) 1 (* n (factorial (- n 1)))))")
(assert-rejected "hc-6 define-lambda factorial under (zero? n): rejected"
  "(define fact (lambda (n) (if (zero? n) 1 (* n (fact (- n 1))))))")
(assert-rejected "hc-6 letrec countdown under (zero? n): rejected"
  "(letrec ((f (lambda (n) (if (zero? n) 0 (f (- n 1)))))) (f 10))")
(assert-rejected "hc-6 cond countdown under (zero? n): rejected"
  "(define (f n) (cond ((zero? n) 0) (else (f (- n 1)))))")
(assert-rejected "hc-6 countdown under unless (= n 0): rejected"
  "(define (f n) (unless (= n 0) (f (- n 1))))")
(assert-rejected "hc-6 countdown under when (not (= n 0)): rejected"
  "(define (f n) (when (not (= n 0)) (f (- n 1))))")
(assert-rejected "hc-6 (- n 2) can step over (= n 0): rejected"
  "(define (f n) (if (= n 0) 0 (f (- n 2)))) (f 3)")
(assert-rejected "hc-6 even/odd under (= n 0): rejected"
  "(define (ev n) (if (= n 0) #t (od (- n 1)))) (define (od n) (if (= n 0) #f (ev (- n 1)))) (ev 4)")
(assert-rejected "hc-6 letrec even/odd under (= n 0): rejected"
  "(letrec ((ev (lambda (n) (if (= n 0) #t (od (- n 1))))) (od (lambda (n) (if (= n 0) #f (ev (- n 1)))))) (ev 10))")
(assert-rejected "hc-6 named let under (= k 0): rejected"
  "(define (f n) (let loop ((k n)) (if (= k 0) 0 (loop (- k 1)))))")
(assert-rejected "hc-6 named let under (zero? n) with sub1: rejected"
  "(let loop ((n 10)) (if (zero? n) 0 (loop (sub1 n))))")
(assert-rejected "hc-6 anonymous self-application under (= n 0): rejected"
  "(define (k) ((lambda (s) (s s 3)) (lambda (self n) (if (= n 0) 0 (self self (- n 1)))))) (display (k))")
(assert-rejected "hc-6 do-loop countdown to (zero? n): rejected"
  "(do ((n 10 (- n 1))) ((zero? n) 0))")
(assert-rejected "hc-6 do-loop countdown to (= n 0): rejected"
  "(do ((n 10 (- n 1))) ((= n 0) 0))")

;; The rejection names the lower stop that fixes it.
(define (reason-mentions? source text)
  (exists (lambda (v)
            (let ((r (termination-violation-reason v)) (n (string-length text)))
              (let loop ((i 0))
                (and (<= (+ i n) (string-length r))
                     (or (string=? (substring r i (+ i n)) text)
                         (loop (+ i 1)))))))
          (check-source-termination source)))
(assert-true "hc-6 direct recursion reason names (<= n 0)"
  (reason-mentions? "(define (f n) (if (= n 0) 0 (f (- n 1))))" "(<= n 0)"))
(assert-true "hc-6 zero? reason names (<= x 0)"
  (reason-mentions? "(define (f x) (if (zero? x) 0 (f (- x 1))))" "(<= x 0)"))
(assert-true "hc-6 named let reason names (<= k 0)"
  (reason-mentions? "(define (f n) (let loop ((k n)) (if (= k 0) 0 (loop (- k 1)))))" "(<= k 0)"))
(assert-true "hc-6 mutual recursion reason names (<= n 0)"
  (reason-mentions? "(define (ev n) (if (= n 0) #t (od (- n 1)))) (define (od n) (if (= n 0) #f (ev (- n 1))))" "(<= n 0)"))
(assert-true "hc-6 do-loop reason names (<= n 0)"
  (reason-mentions? "(do ((n 10 (- n 1))) ((zero? n) 0))" "(<= n 0)"))
(assert-true "hc-6 equality stop on a nonzero bound names (<= n 1)"
  (reason-mentions? "(define (f n) (if (= n 1) 0 (f (- n 1))))" "(<= n 1)"))
(assert-true "hc-6 a stop with no equality test gets no hint"
  (not (reason-mentions? "(define (f n) (f (- n 1)))" "(<=")))
(assert-true "hc-6 ascent to (= i 0) gets no hint"
  (not (reason-mentions? "(define (f i) (if (= i 0) 0 (f (+ i 1)))) (f -5)" "(<=")))
(assert-true "hc-6 do-loop ascent to (= i 0) gets no hint"
  (not (reason-mentions? "(do ((i -5 (+ i 1))) ((= i 0) 0))" "(<=")))
(assert-true "hc-6 equality test on a variable that does not descend gets no hint"
  (not (reason-mentions? "(define (f n m) (if (= m 0) 0 (f (- n 1) m)))" "(<= m")))

;; Lower stops still accepted.
(assert-no-violations "hc-6 countdown under (< n 1): accepted"
  (check-source-termination "(define (f n) (if (< n 1) 0 (f (- n 1)))) (f -1)"))
(assert-no-violations "hc-6 countdown under (<= n 0) then (= n 5): accepted"
  (check-source-termination "(define (f n) (cond ((<= n 0) 0) ((= n 5) 5) (else (f (- n 1)))))"))
(assert-no-violations "hc-6 list walk under (null? l) unaffected: accepted"
  (check-source-termination "(define (f l) (if (null? l) 0 (+ 1 (f (cdr l)))))"))

;; ============================================================
;; HC-8: the false branch of a lower-pass test on a formal is a base case
;; ============================================================

(assert-no-violations "hc-8 (if (> n 0) <rec> 0): accepted"
  (check-source-termination "(define (f n) (if (> n 0) (f (- n 1)) 0))"))
(assert-no-violations "hc-8 (if (>= n 1) <rec> 0): accepted"
  (check-source-termination "(define (f n) (if (>= n 1) (f (- n 1)) 0))"))
(assert-no-violations "hc-8 (if (positive? n) <rec> 0): accepted"
  (check-source-termination "(define (f n) (if (positive? n) (f (- n 1)) 0))"))
(assert-no-violations "hc-8 mirrored (if (< 0 n) <rec> 0): accepted"
  (check-source-termination "(define (f n) (if (< 0 n) (f (- n 1)) 0))"))
(assert-no-violations "hc-8 recursion nested in the true branch: accepted"
  (check-source-termination "(define (f n) (if (> n 0) (+ 1 (f (- n 1))) 0))"))
(assert-no-violations "hc-8 accumulator returned on the false branch: accepted"
  (check-source-termination "(define (f n acc) (if (> n 0) (f (- n 1) (* acc n)) acc))"))
(assert-no-violations "hc-8 one-armed if: accepted"
  (check-source-termination "(define (f n) (if (> n 0) (f (- n 1))))"))
(assert-no-violations "hc-8 cond falling through after a pass test: accepted"
  (check-source-termination "(define (f n) (cond ((> n 0) (f (- n 1)))))"))
(assert-no-violations "hc-8 cond with else after a pass test: accepted"
  (check-source-termination "(define (f n) (cond ((> n 0) (f (- n 1))) (else 0)))"))
(assert-no-violations "hc-8 unless spelling, accepted before HC-8 too: accepted"
  (check-source-termination "(define (f n) (unless (<= n 0) (f (- n 1))))"))
(assert-no-violations "hc-8 named let: accepted"
  (check-source-termination "(let loop ((n 10)) (if (> n 0) (loop (- n 1)) 0))"))
(assert-no-violations "hc-8 mutual recursion: accepted"
  (check-source-termination "(define (ev n) (if (> n 0) (od (- n 1)) #t)) (define (od n) (if (> n 0) (ev (- n 1)) #f))"))
(assert-no-violations "hc-8 anonymous lambda recursion: accepted"
  (check-source-termination "(define (g x) ((lambda (h) (h h x)) (lambda (h n) (if (> n 0) (h h (- n 1)) 0))))"))

;; The false branch still has to stop. Each case descends structurally on l,
;; so only the base-case rule can reject it.
(define (hc-8-kinds src)
  (map termination-violation-kind (check-source-termination src)))
(assert-true "hc-8 false branch that recurses: no-base-case"
  (and (memq 'no-base-case
             (hc-8-kinds "(define (f l n) (if (> n 0) (f (cdr l) n) (f (cdr l) n)))"))
       #t))
(assert-true "hc-8 mutual pair whose false branches recurse: no-base-case"
  (and (memq 'no-base-case
             (hc-8-kinds "(define (ev l n) (if (> n 0) (od (cdr l) n) (od (cdr l) n))) (define (od l n) (if (> n 0) (ev (cdr l) n) (ev (cdr l) n)))"))
       #t))
(assert-true "hc-8 cond whose last clause is not the pass test: no-base-case"
  (and (memq 'no-base-case
             (hc-8-kinds "(define (f l n) (cond ((> n 0) (f (cdr l) n)) (#t (f (cdr l) n))))"))
       #t))
(assert-true "hc-8 cond fall-through whose test recurses: no-base-case"
  (and (memq 'no-base-case
             (hc-8-kinds "(define (f l n) (cond ((> n (f (cdr l) 0)) (f (cdr l) n))))"))
       #t))
(assert-true "hc-8 if whose pass test recurses: no-base-case"
  (and (memq 'no-base-case
             (hc-8-kinds "(define (f l n) (if (> n (f (cdr l) 0)) (f (cdr l) n)))"))
       #t))
(assert-equal "hc-8 pass test on a global, not a formal: rejected"
  #f (null? (check-source-termination "(define m 3) (define (f n) (if (> m 0) (f (- n 1)) 0))")))
;; Known limitation, matching (<= n m) on master: a bound that is another
;; formal is not credited, although this program terminates.
(assert-equal "hc-8 pass test against another formal: still rejected"
  #f (null? (check-source-termination "(define (f n m) (if (> n m) (f (- n 1) m) 0))")))

;; ============================================================
;; HC-9: a rest formal is never a stable guard bound
;; ============================================================
(newline)
(display "=== HC-9: rest formals in guard bounds ===") (newline)
;; Each call rebinds the rest formal to a fresh list, so (car m) can move
;; between calls. A Chez run of this went 100,000 calls without stopping.
(assert-equal "hc-9 anonymous cycle bounded by (car rest): rejected"
  #f (null? (check-source-termination "(define (g x) ((lambda (h) (h h x 0)) (lambda (h n . m) (if (<= n (car m)) 0 (h h (- n 1) (- (car m) 2))))))")))
(assert-equal "hc-9 definition bounded by (car rest): rejected"
  #f (null? (check-source-termination "(define (f n . m) (if (<= n (car m)) 0 (f (- n 1) (- (car m) 2))))")))
(assert-no-violations "hc-9 anonymous cycle with a constant bound: accepted"
  (check-source-termination "(define (g x) ((lambda (h) (h h x 0)) (lambda (h n . m) (if (<= n 0) 0 (h h (- n 1) (car m))))))"))

;; ============================================================
;; Results
;; ============================================================
(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)
(when (> fail-count 0)
  (exit 1))
