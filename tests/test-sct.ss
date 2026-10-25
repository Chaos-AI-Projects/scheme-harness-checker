;; test-sct.ss
;; Unit tests for the size-change termination core (HC-2).
;;
;; Run with: scheme --libdirs ../src --program test-sct.ss

(import (rnrs)
        (harness-checker sct))

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

;; A graph's arcs as a sorted list, so tests do not depend on arc order.
(define (arcs-of g)
  (list-sort (lambda (a b) (string<? (arc->string a) (arc->string b)))
             (sc-graph-arcs g)))

(define (arc->string a)
  (call-with-string-output-port (lambda (p) (write a p))))

(display "--- graphs ---") (newline)

(assert-equal "duplicate arcs merge, strict wins"
  '((x y #t))
  (arcs-of (make-sc-graph 'f 'g '((x y #f) (x y #t) (x y #f)))))

(assert-equal "graph keeps its endpoints"
  '(f g)
  (let ((g (make-sc-graph 'f 'g '())))
    (list (sc-graph-src g) (sc-graph-dst g))))

(display "--- composition ---") (newline)

(assert-equal "non-strict then strict is strict"
  '((t t #t))
  (arcs-of (sc-compose (make-sc-graph 'tree-sum 'my-map '((t l #f)))
                       (make-sc-graph 'my-map 'tree-sum '((l t #t))))))

(assert-equal "non-strict then non-strict is non-strict"
  '((x z #f))
  (arcs-of (sc-compose (make-sc-graph 'f 'g '((x y #f)))
                       (make-sc-graph 'g 'h '((y z #f))))))

(assert-equal "an arc needs both halves"
  '()
  (arcs-of (sc-compose (make-sc-graph 'f 'g '((x y #t)))
                       (make-sc-graph 'g 'h '((w z #t))))))

(assert-equal "two paths to one arc keep the strict one"
  '((x z #t))
  (arcs-of (sc-compose (make-sc-graph 'f 'g '((x a #f) (x b #t)))
                       (make-sc-graph 'g 'h '((a z #f) (b z #f))))))

(assert-equal "argument swap composes to strict self-arcs"
  '((x x #t) (y y #t))
  (arcs-of (let ((g (make-sc-graph 'f 'f '((x y #t) (y x #f)))))
             (sc-compose g g))))

(display "--- criterion ---") (newline)

(assert-equal "empty graph set terminates"
  'terminates
  (sc-check '() 1000))

(assert-equal "direct recursion with a strict self-arc terminates"
  'terminates
  (sc-check (list (make-sc-graph 'f 'f '((n n #t)))) 1000))

(assert-equal "direct recursion with only a non-strict arc does not"
  'no-descent
  (sc-check (list (make-sc-graph 'f 'f '((n n #f)))) 1000))

(assert-equal "direct recursion with no arcs does not"
  'no-descent
  (sc-check (list (make-sc-graph 'f 'f '())) 1000))

(assert-equal "tree-sum through my-map terminates"
  'terminates
  (sc-check (list (make-sc-graph 'tree-sum 'my-map '((t l #f)))
                  (make-sc-graph 'my-map 'my-map '((g g #f) (l l #t)))
                  (make-sc-graph 'my-map 'tree-sum '((l t #t))))
            1000))

;; (define (f x y) (if (<= x 0) 0 (f y (- x 1))))
(assert-equal "argument swap terminates"
  'terminates
  (sc-check (list (make-sc-graph 'f 'f '((x y #t) (y x #f)))) 1000))

;; (define (f x y) (if (<= x 0) 0 (f (+ y 1) (- x 1))))
(assert-equal "swap with growth does not"
  'no-descent
  (sc-check (list (make-sc-graph 'f 'f '((x y #t)))) 1000))

;; Each edge alone decreases something, but the path f->g->f does not:
;; f passes x down strictly as a, g passes b (not a) back as x.
(assert-equal "a cycle that decreases per edge but not round the loop"
  'no-descent
  (sc-check (list (make-sc-graph 'f 'g '((x a #t)))
                  (make-sc-graph 'g 'f '((b x #t))))
            1000))

(assert-equal "mutual recursion that decreases round the loop terminates"
  'terminates
  (sc-check (list (make-sc-graph 'even? 'odd? '((n n #t)))
                  (make-sc-graph 'odd? 'even? '((n n #t))))
            1000))

(assert-equal "the cap rejects with size-change-limit"
  'limit
  (sc-check (list (make-sc-graph 'f 'f '((a b #f) (b c #f) (c a #t)))
                  (make-sc-graph 'f 'f '((a a #f) (b c #t) (c b #f))))
            2))

(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)
(exit (if (= fail-count 0) 0 1))
