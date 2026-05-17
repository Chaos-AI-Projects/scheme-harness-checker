;; test-termination.ss
;; Tests for the termination analysis pass.
;;
;; Run with: scheme --libdirs ../src --program test-termination.ss

(import (rnrs)
        (harness-checker termination)
        (harness-checker whitelist-checker))

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
    "(define (factorial n) (if (= n 0) 1 (* n (factorial (- n 1)))))"))

(assert-no-violations "valid do loop"
  (check-source-termination
    "(do ((i 0 (+ i 1))) ((= i 10) i) (display i))"))

(assert-no-violations "named let loop with decreasing arg and base case"
  (check-source-termination
    "(let loop ((i 0)) (when (< i 10) (display i) (loop (+ i 1))))"))

(assert-no-violations "mutual recursion (valid even?/odd?)"
  (check-source-termination
    "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (= n 0) #f (even? (- n 1))))"))

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
    "(do ((i 0 (+ i 1)) (j 10 (- j 1))) ((= i j)) (display i))"))

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
    "(let loop ((n 10)) (if (= n 0) 0 (loop (- n 1))))"))

(assert-no-violations "named-let with sub1 decrease"
  (check-source-termination
    "(let loop ((n 10)) (if (zero? n) 0 (loop (sub1 n))))"))

(assert-no-violations "named-let with fx- decrease"
  (check-source-termination
    "(let loop ((n 10)) (if (= n 0) 0 (loop (fx- n 1))))"))

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
    "(let loop ((n 10)) (unless (= n 0) (display n) (loop (- n 1))))"))

(assert-no-violations "named-let with cond guard"
  (check-source-termination
    "(let loop ((n 10)) (cond ((= n 0) 'done) (else (loop (- n 1)))))"))

(assert-no-violations "named-let with multiple args, one decreasing"
  (check-source-termination
    "(let loop ((n 10) (acc 0)) (if (= n 0) acc (loop (- n 1) (+ acc n))))"))

(assert-no-violations "named-let nested inside define"
  (check-source-termination
    "(define (sum-to n) (let loop ((i n) (acc 0)) (if (= i 0) acc (loop (- i 1) (+ acc i)))))"))

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
    "(let outer ((i 10)) (if (= i 0) 0 (let inner ((j 5)) (if (= j 0) (outer (- i 1)) (inner (- j 1))))))"))

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
    "(let loop ((n 10)) (if (= n 0) 0 (loop (- n 1))))"))

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
    "(let loop ((n 10)) (unless (= n 0) (display n) (loop (- n 1))))"))

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
    "(let loop ((x 10)) (if (zero? x) 'done (if (even? x) (loop (- x 1)) (loop (- x 2)))))"))

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
    "(define (fact n) (if (zero? n) 1 (* n (fact (- n 1)))))"))

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
    "(define fact (lambda (n) (if (zero? n) 1 (* n (fact (- n 1))))))"))

;; letrec-bound recursive function with decrease + base case
(assert-no-violations "direct recursion: letrec with decrease + base passes"
  (check-source-termination
    "(letrec ((f (lambda (n) (if (zero? n) 0 (f (- n 1)))))) (f 10))"))

;; sub1 decrease pattern
(assert-no-violations "direct recursion: sub1 decrease passes"
  (check-source-termination
    "(define (count n) (if (zero? n) 0 (count (sub1 n))))"))

;; cond-based base case
(assert-no-violations "direct recursion: cond base case passes"
  (check-source-termination
    "(define (f n) (cond ((zero? n) 0) (else (f (- n 1)))))"))

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

;; Increasing argument (not decreasing)
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
    "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (= n 0) #f (even? (- n 1))))"))

;; ============================================================
;; Test Group: Mutual recursion analysis - valid patterns (no violations)
;; ============================================================
(display "=== Mutual recursion analysis: valid ===") (newline)

;; Issue #275 test 1: even?/odd? with (- n 1) and base cases
(assert-no-violations "mutual recursion: even?/odd? with decrease and base case"
  (check-source-termination
    (string-append
      "(define (my-even? n) (if (= n 0) #t (my-odd? (- n 1)))) "
      "(define (my-odd? n) (if (= n 0) #f (my-even? (- n 1))))")))

;; Three-function cycle all decreasing
(assert-no-violations "mutual recursion: three-function cycle with decrease"
  (check-source-termination
    (string-append
      "(define (a n) (if (= n 0) 'done (b (- n 1)))) "
      "(define (b n) (if (= n 0) 'done (c (- n 1)))) "
      "(define (c n) (if (= n 0) 'done (a (- n 1))))")))

;; Both functions decrease on their respective calls
(assert-no-violations "mutual recursion: both functions decrease before calling partner"
  (check-source-termination
    (string-append
      "(define (ping n) (if (= n 0) 'done (pong (- n 1)))) "
      "(define (pong n) (if (= n 0) 'done (ping (- n 1))))")))

;; letrec-bound mutual recursion
(assert-no-violations "mutual recursion: letrec-bound even/odd"
  (check-source-termination
    (string-append
      "(letrec ((ev (lambda (n) (if (= n 0) #t (od (- n 1))))) "
      "         (od (lambda (n) (if (= n 0) #f (ev (- n 1)))))) "
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
                      "(define (countdown n) (let loop ((i n)) (if (= i 0) 'done (loop (- i 1))))) "
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
                      "  (let ((inner (lambda (m) (if (= m 0) 'done (inner (- m 1)))))) "
                      "    (if (= n 0) 'base (outer (- n 1)))))"))))
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
      "                   (if (zero? n) acc (fact (- n 1) (* acc n)))))) "
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

;; check-termination with depth limit of 0 should skip call-graph analysis
;; (only do-form and named-let checks run)
(let ((violations (check-termination
                    (read-all-expressions "(define (f n) (f n))")
                    '()
                    0)))  ;; depth-limit = 0 skips call-graph phases
  (assert-no-violations "depth-limit 0: skips direct recursion check" violations))

;; With no depth limit (default), direct recursion is caught
(let ((violations (check-termination
                    (read-all-expressions "(define (f n) (f n))")
                    '())))
  (assert-violation-count "no depth-limit: catches direct recursion" 1 violations))

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
