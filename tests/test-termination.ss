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
;; Test Group: Stub returns empty list
;; ============================================================
(display "=== Stub returns empty list ===") (newline)

(assert-no-violations "empty input"
  (check-source-termination ""))

(assert-no-violations "simple arithmetic"
  (check-source-termination "(+ 1 2)"))

(assert-no-violations "define and call"
  (check-source-termination "(define (f x) (+ x 1)) (f 42)"))

(assert-no-violations "recursive function (stub ignores)"
  (check-source-termination
    "(define (factorial n) (if (= n 0) 1 (* n (factorial (- n 1)))))"))

(assert-no-violations "do loop (stub ignores)"
  (check-source-termination
    "(do ((i 0 (+ i 1))) ((= i 10) i) (display i))"))

(assert-no-violations "named let loop (stub ignores)"
  (check-source-termination
    "(let loop ((i 0)) (when (< i 10) (display i) (loop (+ i 1))))"))

(assert-no-violations "mutual recursion (stub ignores)"
  (check-source-termination
    "(define (even? n) (if (= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (= n 0) #f (even? (- n 1))))"))

(assert-no-violations "infinite loop pattern (stub ignores)"
  (check-source-termination
    "(let loop () (display \"forever\") (loop))"))

;; ============================================================
;; Test Group: Return type is list
;; ============================================================
(display "=== Return type ===") (newline)

(assert-true "result is a list"
  (list? (check-source-termination "(define (f x) x)")))

(assert-equal "result is empty list"
  '()
  (check-source-termination "(define (f x) x)"))

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
