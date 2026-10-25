;; test-cfa.ss
;; Unit tests for the 0CFA call-site table (HC-2).
;;
;; Run with: scheme --libdirs ../src --program test-cfa.ss

(import (rnrs)
        (harness-checker cfa)
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

(define (analyze source)
  (cfa-analyze (read-all-expressions source)))

;; A lambda's display name: its bound symbol, else its label.
(define (lambda-name result label)
  (or (cfa-lambda-name (cfa-lambda-ref result label)) label))

;; Every call site whose expression is equal? to `datum`, as a list of
;; (caller-name . callee-names). The top level is named `top`.
(define (callees-at source datum)
  (let ((r (analyze source)))
    (map (lambda (s)
           (cons (if (cfa-site-caller s) (lambda-name r (cfa-site-caller s)) 'top)
                 (map (lambda (l) (lambda-name r l)) (cfa-site-callee-labels s))))
         (filter (lambda (s) (equal? (cfa-site-expr s) datum))
                 (cfa-result-sites r)))))

(define (site-unresolved? source datum)
  (let ((r (analyze source)))
    (exists (lambda (s) (and (equal? (cfa-site-expr s) datum)
                             (cfa-site-unresolved? s)))
            (cfa-result-sites r))))

(display "--- direct calls ---") (newline)

(assert-equal "direct call to a define"
  '((f g))
  (callees-at "(define (f x) (g x)) (define (g y) y)" '(g x)))

(assert-equal "call to a built-in has no callees"
  '((f))
  (callees-at "(define (f x) (car x))" '(car x)))

(display "--- the HC-2 loops ---") (newline)

(assert-equal "omega: outer site calls the first lambda"
  '((top 0))
  (callees-at "((lambda (x) (x x)) (lambda (x) (x x)))"
              '((lambda (x) (x x)) (lambda (x) (x x)))))

(assert-equal "omega: both (x x) sites call the second lambda"
  '((0 1) (1 1))
  (callees-at "((lambda (x) (x x)) (lambda (x) (x x)))" '(x x)))

(assert-equal "self-application through a formal"
  '((f f))
  (callees-at "(define (f g) (g g)) (f f)" '(g g)))

(assert-equal "alias through let"
  '((loop loop))
  (callees-at "(define (loop n) (let ((h loop)) (h n))) (loop 3)" '(h n)))

(assert-equal "recursion through map"
  '((f f))
  (callees-at "(define (f x) (map f (list x))) (f 1)" '(map f (list x))))

(assert-equal "anonymous self-application inside a define"
  '((1 1))
  (callees-at "(define (f) (let ((g (lambda (h) (h h)))) (g g))) (f)" '(h h)))

(display "--- data structures ---") (newline)

(assert-equal "lambda stored with cons and read with car"
  '((f f))
  (callees-at "(define (f x) ((car (cons f '())) x))" '((car (cons f '())) x)))

(assert-equal "cdr returns the rest of a list"
  '((f g))
  (callees-at "(define (g) 0) (define (f) ((cadr (list 1 g))))" '((cadr (list 1 g)))))

(assert-equal "vector-set! then vector-ref"
  '((f g))
  (callees-at
   (string-append "(define (g) 1) "
                  "(define (f v) (vector-set! v 0 g) ((vector-ref v 0))) "
                  "(f (make-vector 1 0))")
   '((vector-ref v 0))))

(assert-equal "quasiquote holds an unquoted lambda"
  '((f g))
  (callees-at "(define (g) 1) (define (f) ((car `(,g))))" '((car `(,g)))))

(display "--- apply and HOFs ---") (newline)

(assert-equal "apply with leading and list arguments"
  '((f h))
  (callees-at "(define (h a b) a) (define (f) (apply h 1 (list 2)))"
              '(apply h 1 (list 2))))

(assert-equal "apply spreads a list of lambdas into the formals"
  '((f k))
  (callees-at "(define (k) 0) (define (f g) (g)) (apply f (list k))" '(g)))

(assert-equal "HOF callback receives list elements"
  '((2 k))
  (callees-at "(define (k) 0) (define (f) (for-each (lambda (g) (g)) (list k)))"
              '(g)))

(assert-equal "fold-left accumulator flows back to the callback"
  '((2 k))
  (callees-at
   "(define (k) 0) (define (f) (fold-left (lambda (acc x) (acc)) k (list 1)))"
   '(acc)))

(assert-equal "a built-in passed as a callback adds no callees"
  '((f))
  (callees-at "(define (f l) (for-each display l))" '(for-each display l)))

(display "--- binding forms ---") (newline)

(assert-equal "named let loop calls itself"
  '((loop loop))
  (callees-at "(define (f n) (let loop ((i n)) (if (= i 0) 0 (loop (- i 1)))))"
              '(loop (- i 1))))

(assert-equal "letrec binding"
  '((top ev))
  (callees-at "(letrec ((ev (lambda (n) n))) (ev 1))" '(ev 1)))

(assert-equal "set! adds to a variable"
  '((f g))
  (callees-at "(define (g) 1) (define (f) (let ((h 0)) (set! h g) (h)))" '(h)))

(assert-equal "inner binding shadows an outer name"
  '((f))
  (callees-at "(define (g) 1) (define (f g) (g)) (f 2)" '(g)))

(assert-equal "case-lambda dispatches on arity"
  1
  (let* ((r (analyze "(define f (case-lambda ((x) x) ((x y) (f x))))"))
         (s (find (lambda (s) (equal? (cfa-site-expr s) '(f x)))
                  (cfa-result-sites r))))
    (length (cfa-site-callee-labels s))))

(assert-equal "cond => invokes the procedure"
  '((f g))
  (callees-at "(define (g x) x) (define (f y) (cond (y => g) (else 0)))"
              '(y => g)))

(display "--- lambda records ---") (newline)

(let ((r (analyze "(define (f g) (g g)) (letrec ((h (lambda () 0))) (h))")))
  (assert-equal "define gets kind define and its name"
    '(define f #f)
    (let ((l (cfa-lambda-ref r 0)))
      (list (cfa-lambda-kind l) (cfa-lambda-name l) (cfa-lambda-parent l))))
  (assert-equal "letrec binding gets kind letrec"
    '(letrec h)
    (let ((l (cfa-lambda-ref r 1)))
      (list (cfa-lambda-kind l) (cfa-lambda-name l)))))

(let ((r (analyze "(define (f n) (for-each (lambda (x) x) n))")))
  (assert-equal "an inner lambda records its parent"
    '(lambda #f 0)
    (let ((l (cfa-lambda-ref r 1)))
      (list (cfa-lambda-kind l) (cfa-lambda-name l) (cfa-lambda-parent l)))))

(display "--- fail-closed ---") (newline)

(assert-equal "a value returned by an unmodeled operator is unresolved"
  #t
  (site-unresolved? "(define (f x) ((tool-get x f)))" '((tool-get x f))))

(assert-equal "a lambda handed to an unmodeled operator escapes"
  '((f f))
  (callees-at "(define (f x) (tool-run f))" '(tool-run f)))

(assert-equal "opaque data in operator position is not unresolved"
  #f
  (site-unresolved? "(define (f x) ((car (list (+ x 1)))))"
                    '((car (list (+ x 1))))))

(assert-equal "an unmodeled operator given only data returns data"
  #f
  (site-unresolved? "(define (f x) ((tool-get 1)))" '((tool-get 1))))

;; The whitelist has no procedure-returning built-in, so opaque data can
;; never reach operator position. If a signature ever gains a function
;; return type, cfa.ss must model that built-in.
(define signatures
  (call-with-input-file "../data/type-signatures.scm" read))

(define (function-type? t)
  (and (pair? t) (memq (car t) '(-> ->*)) #t))

(define (return-type sig)
  (if (function-type? sig) (list-ref sig (- (length sig) 1)) sig))

(assert-equal "no whitelisted built-in returns a procedure"
  '()
  (map car (filter (lambda (e) (function-type? (return-type (cdr e))))
                   signatures)))

(assert-equal "every whitelisted built-in is modeled by cfa.ss"
  '()
  (map car (filter (lambda (e) (not (cfa-modeled-builtin? (car e))))
                   signatures)))

(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)
(exit (if (= fail-count 0) 0 1))
