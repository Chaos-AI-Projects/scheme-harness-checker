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

(assert-no-violations "recursive function (no violations yet)"
  (check-source-termination
    "(define (factorial n) (if (= n 0) 1 (* n (factorial (- n 1)))))"))

(assert-no-violations "do loop (no violations yet)"
  (check-source-termination
    "(do ((i 0 (+ i 1))) ((= i 10) i) (display i))"))

(assert-no-violations "named let loop (no violations yet)"
  (check-source-termination
    "(let loop ((i 0)) (when (< i 10) (display i) (loop (+ i 1))))"))

(assert-no-violations "mutual recursion (no violations yet)"
  (check-source-termination
    "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (= n 0) #f (even? (- n 1))))"))

(assert-no-violations "infinite loop pattern (no violations yet)"
  (check-source-termination
    "(let loop () (display \"forever\") (loop))"))

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
;; Results
;; ============================================================
(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)
(when (> fail-count 0)
  (exit 1))
