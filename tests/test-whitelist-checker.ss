;; test-whitelist-checker.ss
;; Tests for the whitelist checker's abstract evaluator and identifier collection.
;;
;; Run with: scheme --libdirs ../src --program test-whitelist-checker.ss

(import (rnrs) (harness-checker whitelist-checker))

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

(define (assert-violations-empty test-name violations)
  (assert-equal test-name '() (map wl-violation-identifier violations)))

(define (assert-violations test-name expected-ids violations)
  (let ((actual-ids (map wl-violation-identifier violations)))
    (assert-equal test-name
                  (list-sort symbol<? expected-ids)
                  (list-sort symbol<? actual-ids))))

(define (symbol<? a b)
  (string<? (symbol->string a) (symbol->string b)))

;; --- Test: basic define binds the name ---
(display "Test group: define") (newline)

(let ((violations (check-source "(define x 42) x" '())))
  (assert-violations-empty "define binds variable" violations))

(let ((violations (check-source "(define (f a b) (+ a b)) (f 1 2)" '(+))))
  (assert-violations-empty "define function binds name and params" violations))

(let ((violations (check-source "(define (f x) (g x))" '())))
  (assert-violations "unbound function in body" '(g) violations))

;; --- Test: lambda ---
(display "Test group: lambda") (newline)

(let ((violations (check-source "((lambda (x) x) 42)" '())))
  (assert-violations-empty "lambda binds params" violations))

(let ((violations (check-source "((lambda (x) (+ x 1)) 42)" '(+))))
  (assert-violations-empty "lambda with whitelisted +" violations))

(let ((violations (check-source "((lambda (x) (+ x 1)) 42)" '())))
  (assert-violations "lambda uses unwhitelisted +" '(+) violations))

(let ((violations (check-source "(lambda args (apply + args))" '(apply +))))
  (assert-violations-empty "lambda rest parameter" violations))

;; --- Test: let ---
(display "Test group: let") (newline)

(let ((violations (check-source "(let ((x 1) (y 2)) (+ x y))" '(+))))
  (assert-violations-empty "let binds variables" violations))

(let ((violations (check-source "(let ((x 1)) (+ x y))" '(+))))
  (assert-violations "let does not bind y" '(y) violations))

;; named let
(let ((violations (check-source
                   "(let loop ((n 10) (acc 0)) (if (zero? n) acc (loop (- n 1) (+ acc n))))"
                   '(zero? - +))))
  (assert-violations-empty "named let binds loop and params" violations))

;; --- Test: letrec ---
(display "Test group: letrec") (newline)

(let ((violations (check-source
                   "(letrec ((even? (lambda (n) (if (= n 0) #t (odd? (- n 1))))) (odd? (lambda (n) (if (= n 0) #f (even? (- n 1)))))) (even? 10))"
                   '(= -))))
  (assert-violations-empty "letrec mutual recursion" violations))

;; --- Test: nested scoping ---
(display "Test group: nested scoping") (newline)

(let ((violations (check-source
                   "(define (outer x) (let ((y (+ x 1))) (define (inner z) (* y z)) (inner y)))"
                   '(+ *))))
  (assert-violations-empty "nested define inside let" violations))

;; --- Test: top-level body defines are mutually visible ---
(display "Test group: top-level mutual visibility") (newline)

(let ((violations (check-source
                   "(define (f x) (g x)) (define (g x) (* x 2))"
                   '(*))))
  (assert-violations-empty "top-level defines see each other" violations))

;; --- Test: forbidden forms ---
(display "Test group: forbidden forms") (newline)

(let ((violations (check-source "(define-syntax my-macro (syntax-rules () ((my-macro x) x)))" '())))
  (assert-violations "define-syntax is flagged"
                     '(define-syntax syntax-rules)
                     violations))

;; --- Test: set! ---
(display "Test group: set!") (newline)

(let ((violations (check-source "(define x 0) (set! x 1)" '())))
  (assert-violations-empty "set! on bound variable" violations))

(let ((violations (check-source "(set! x 1)" '())))
  (assert-violations "set! on unbound variable" '(x) violations))

;; --- Test: quote is not walked ---
(display "Test group: quote") (newline)

(let ((violations (check-source "'(dangerous-fn evil system)" '())))
  (assert-violations-empty "quoted symbols are not checked" violations))

;; --- Test: do ---
(display "Test group: do") (newline)

(let ((violations (check-source
                   "(do ((i 0 (+ i 1))) ((= i 10) i) (display i))"
                   '(+ = display))))
  (assert-violations-empty "do binds iteration vars" violations))

(let ((violations (check-source
                   "(do ((i 0 (+ i 1)) (j 10 (- j 1))) ((= i j) (+ i j)) (display i) (display j))"
                   '(+ - = display))))
  (assert-violations-empty "do multiple bindings" violations))

(let ((violations (check-source
                   "(do ((i 0 (+ i 1))) ((= i n)) (display i))"
                   '(+ = display))))
  (assert-violations "do body references unbound n" '(n) violations))

;; --- Test: let-values ---
(display "Test group: let-values") (newline)

(let ((violations (check-source
                   "(let-values (((a b) (values 1 2))) (+ a b))"
                   '(+ values))))
  (assert-violations-empty "let-values binds variables" violations))

(let ((violations (check-source
                   "(let-values (((x y z) (get-coords))) (+ x y z))"
                   '(+ get-coords))))
  (assert-violations-empty "let-values with 3 bindings" violations))

(let ((violations (check-source
                   "(let-values (((a b) (values 1 2))) (+ a b c))"
                   '(+ values))))
  (assert-violations "let-values does not bind c" '(c) violations))

;; --- Test: case ---
(display "Test group: case") (newline)

(let ((violations (check-source
                   "(case x ((foo bar) 1) ((baz) 2) (else 3))"
                   '())))
  (assert-violations "case key expr unbound but datums not flagged" '(x) violations))

(let ((violations (check-source
                   "(define x 5) (case x ((1 2 3) (display \"low\")) ((4 5 6) (display \"mid\")) (else (display \"high\")))"
                   '(display))))
  (assert-violations-empty "case with bound key and whitelisted body" violations))

(let ((violations (check-source
                   "(case (get-val) ((alpha beta gamma) (process alpha)) (else (fallback)))"
                   '(get-val process fallback))))
  (assert-violations "case datum symbols not walked as expressions" '(alpha) violations))

;; Verify datums that are symbols don't get flagged
(let ((violations (check-source
                   "(define v 1) (case v ((red green blue) \"color\") ((circle square) \"shape\"))"
                   '())))
  (assert-violations-empty "case datum symbols ignored entirely" violations))

;; --- Test: realistic LLM-generated code ---
(display "Test group: realistic LLM code") (newline)

(let ((violations (check-source
                   "(define (fibonacci n)
                      (let loop ((i 0) (a 0) (b 1))
                        (if (= i n)
                            a
                            (loop (+ i 1) b (+ a b)))))
                    (display (fibonacci 10))
                    (newline)"
                   '(= + display newline))))
  (assert-violations-empty "fibonacci with named let" violations))

(let ((violations (check-source
                   "(define (quicksort lst)
                      (if (null? lst)
                          '()
                          (let ((pivot (car lst))
                                (rest (cdr lst)))
                            (append
                              (quicksort (filter (lambda (x) (< x pivot)) rest))
                              (list pivot)
                              (quicksort (filter (lambda (x) (>= x pivot)) rest))))))"
                   '(null? car cdr append filter < >= list))))
  (assert-violations-empty "quicksort uses only whitelisted fns" violations))

;; quicksort with dangerous function
(let ((violations (check-source
                   "(define (bad-sort lst) (system \"rm -rf /\") lst)"
                   '())))
  (assert-violations "dangerous system call detected" '(system) violations))

;; --- Test: let* ---
(display "Test group: let*") (newline)

(let ((violations (check-source "(let* ((x 1) (y (+ x 1))) (+ x y))" '(+))))
  (assert-violations-empty "let* sequential binding" violations))

(let ((violations (check-source "(let* ((x 1) (y (+ x 1)) (z (+ x y))) z)" '(+))))
  (assert-violations-empty "let* three sequential bindings" violations))

(let ((violations (check-source "(let* ((x 1)) (+ x y))" '(+))))
  (assert-violations "let* does not bind y" '(y) violations))

;; --- Test: letrec* ---
(display "Test group: letrec*") (newline)

(let ((violations (check-source
                   "(letrec* ((even? (lambda (n) (if (= n 0) #t (odd? (- n 1))))) (odd? (lambda (n) (if (= n 0) #f (even? (- n 1)))))) (even? 10))"
                   '(= -))))
  (assert-violations-empty "letrec* mutual recursion" violations))

;; --- Test: when/unless ---
(display "Test group: when/unless") (newline)

(let ((violations (check-source "(define x 5) (when (> x 0) (display x))" '(> display))))
  (assert-violations-empty "when with bound variable" violations))

(let ((violations (check-source "(define x 5) (unless (> x 0) (display x))" '(> display))))
  (assert-violations-empty "unless with bound variable" violations))

(let ((violations (check-source "(when flag (action))" '(action))))
  (assert-violations "when with unbound test" '(flag) violations))

;; --- Test: case-lambda ---
(display "Test group: case-lambda") (newline)

(let ((violations (check-source
                   "(define f (case-lambda ((x) (+ x 1)) ((x y) (+ x y))))"
                   '(+))))
  (assert-violations-empty "case-lambda binds params per clause" violations))

(let ((violations (check-source
                   "(define f (case-lambda (() 0) ((x) x) ((x y) (+ x y)) ((x y . rest) (apply + x y rest))))"
                   '(+ apply))))
  (assert-violations-empty "case-lambda multiple arities with rest" violations))

(let ((violations (check-source
                   "(define f (case-lambda ((x) (+ x z))))"
                   '(+))))
  (assert-violations "case-lambda unbound in body" '(z) violations))

;; --- Test: parameterize ---
(display "Test group: parameterize") (newline)

(let ((violations (check-source
                   "(define my-param (make-parameter 10)) (parameterize ((my-param 20)) (my-param))"
                   '(make-parameter))))
  (assert-violations-empty "parameterize with bound parameter" violations))

(let ((violations (check-source
                   "(parameterize ((current-output-port (open-string-output-port))) (display \"hi\"))"
                   '(current-output-port open-string-output-port display))))
  (assert-violations-empty "parameterize with whitelisted functions" violations))

;; --- Test: guard ---
(display "Test group: guard") (newline)

(let ((violations (check-source
                   "(guard (exn ((string? exn) (display exn))) (error \"oops\"))"
                   '(string? display error))))
  (assert-violations-empty "guard binds exception variable" violations))

(let ((violations (check-source
                   "(guard (exn ((message-condition? exn) (condition-message exn)) (else (display \"unknown\"))) (risky-operation))"
                   '(message-condition? condition-message display risky-operation))))
  (assert-violations-empty "guard with else clause" violations))

(let ((violations (check-source
                   "(guard (e ((pair? e) (car e))) (error \"fail\"))"
                   '(pair? car error))))
  (assert-violations-empty "guard simple" violations))

;; --- Test: internal define mutual visibility ---
(display "Test group: internal define mutual visibility") (newline)

(let ((violations (check-source
                   "(define (outer x) (define (f n) (if (= n 0) 1 (g (- n 1)))) (define (g n) (if (= n 0) 1 (f (- n 1)))) (f x))"
                   '(= -))))
  (assert-violations-empty "internal defines are mutually visible" violations))

;; --- Test group: lambda internal define mutual visibility ---
(display "Test group: lambda internal define mutual visibility") (newline)

;; Internal defines inside a lambda body should be mutually visible
(let ((violations (check-source
                   "(lambda (x) (define (f n) (if (= n 0) 1 (g (- n 1)))) (define (g n) (if (= n 0) 1 (f (- n 1)))) (f x))"
                   '(= -))))
  (assert-violations-empty "lambda internal defines are mutually visible" violations))

;; --- Test group: case-lambda internal define mutual visibility ---
(display "Test group: case-lambda internal define mutual visibility") (newline)

;; Internal defines inside a case-lambda clause should be mutually visible
(let ((violations (check-source
                   "(case-lambda ((x) (define (f n) (if (= n 0) 1 (g (- n 1)))) (define (g n) (if (= n 0) 1 (f (- n 1)))) (f x)))"
                   '(= -))))
  (assert-violations-empty "case-lambda internal defines are mutually visible" violations))

;; --- Summary ---
(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed") (newline)

(when (> fail-count 0)
  (exit 1))
