;; test-type-checker.ss
;; Tests for the type checker (Pass 1 constraints + Pass 2 inference).
;;
;; Run with: scheme --libdirs ../src:<packrat-extended-path> --program test-type-checker.ss

(import (rnrs)
        (harness-checker whitelist-checker)
        (harness-checker types)
        (harness-checker pass1-constraints)
        (harness-checker type-infer))

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

(define (assert-no-errors test-name errors)
  (if (null? errors)
      (begin
        (set! pass-count (+ pass-count 1))
        (display "  PASS: ") (display test-name) (newline))
      (begin
        (set! fail-count (+ fail-count 1))
        (display "  FAIL: ") (display test-name) (newline)
        (display "    expected no errors but got ") (display (length errors))
        (newline))))

(define (assert-error-count test-name expected-count errors)
  (let ((actual (length errors)))
    (if (= expected-count actual)
        (begin
          (set! pass-count (+ pass-count 1))
          (display "  PASS: ") (display test-name) (newline))
        (begin
          (set! fail-count (+ fail-count 1))
          (display "  FAIL: ") (display test-name) (newline)
          (display "    expected ") (display expected-count)
          (display " error(s), got ") (display actual) (newline)))))

(define (assert-has-arity-error test-name fn-name errors)
  (let ((found (exists (lambda (e)
                         (and (eq? (type-error-kind e) 'arity)
                              (eq? (type-error-function e) fn-name)))
                       errors)))
    (if found
        (begin
          (set! pass-count (+ pass-count 1))
          (display "  PASS: ") (display test-name) (newline))
        (begin
          (set! fail-count (+ fail-count 1))
          (display "  FAIL: ") (display test-name) (newline)
          (display "    no arity error for ") (display fn-name) (newline)))))

(define (assert-has-type-error test-name fn-name errors)
  (let ((found (exists (lambda (e)
                         (and (eq? (type-error-kind e) 'type-mismatch)
                              (eq? (type-error-function e) fn-name)))
                       errors)))
    (if found
        (begin
          (set! pass-count (+ pass-count 1))
          (display "  PASS: ") (display test-name) (newline))
        (begin
          (set! fail-count (+ fail-count 1))
          (display "  FAIL: ") (display test-name) (newline)
          (display "    no type error for ") (display fn-name) (newline)))))

;; Load signatures for tests
(define signatures (load-type-signatures "data/type-signatures.scm"))

;; Helper: run both passes and return (constraint-errors . type-errors)
(define (check-source-types source)
  (let* ((exprs (read-all-expressions source))
         (pass1-result (infer-param-constraints exprs signatures))
         (param-types (car pass1-result))
         (p1-errors (cdr pass1-result))
         (p2-errors (check-types exprs signatures param-types)))
    (cons p1-errors p2-errors)))

(define (get-constraint-errors result) (car result))
(define (get-type-errors result) (cdr result))

;; ===================================================================
;; Test Group: Type System Basics
;; ===================================================================
(display "Test group: types library") (newline)

(assert-true "Number subtype of Any"
  (subtype? type:number type:any))

(assert-true "Null subtype of List"
  (subtype? type:null (make-type-list type:number)))

(assert-true "Number not subtype of String"
  (not (subtype? type:number type:string)))

(assert-true "List Number subtype of List Any"
  (subtype? (make-type-list type:number) (make-type-list type:any)))

(assert-true "type=? same base"
  (type=? type:number type:number))

(assert-true "type=? different base"
  (not (type=? type:number type:string)))

(assert-true "union simplification single"
  (type=? (simplify-union (list type:number)) type:number))

(assert-true "union simplification dedup"
  (type=? (simplify-union (list type:number type:number)) type:number))

;; ===================================================================
;; Test Group: No Errors on Valid Code
;; ===================================================================
(display "Test group: valid code (no errors)") (newline)

(let ((result (check-source-types "(+ 1 2 3)")))
  (assert-no-errors "variadic arithmetic" (get-type-errors result)))

(let ((result (check-source-types "(string-length \"hello\")")))
  (assert-no-errors "string-length on string literal" (get-type-errors result)))

(let ((result (check-source-types "(car (cons 1 2))")))
  (assert-no-errors "car on cons result" (get-type-errors result)))

(let ((result (check-source-types "(define (f x) (+ x 1)) (f 42)")))
  (assert-no-errors "user function with numeric arg" (get-type-errors result)))

(let ((result (check-source-types "(let ((x 5)) (+ x 3))")))
  (assert-no-errors "let-bound numeric" (get-type-errors result)))

(let ((result (check-source-types "(if #t 1 2)")))
  (assert-no-errors "if expression" (get-type-errors result)))

(let ((result (check-source-types "(map (lambda (x) x) (list 1 2 3))")))
  (assert-no-errors "map with lambda" (get-type-errors result)))

(let ((result (check-source-types "(vector-ref (vector 1 2 3) 0)")))
  (assert-no-errors "vector-ref valid" (get-type-errors result)))

(let ((result (check-source-types
  "(define (fact n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5)")))
  (assert-no-errors "factorial" (get-type-errors result)))

(let ((result (check-source-types "(string-append \"a\" \"b\" \"c\")")))
  (assert-no-errors "variadic string-append" (get-type-errors result)))

;; ===================================================================
;; Test Group: Arity Errors
;; ===================================================================
(display "Test group: arity errors") (newline)

(let* ((result (check-source-types "(car 1 2)"))
       (errors (get-type-errors result)))
  (assert-has-arity-error "car takes exactly 1 arg" 'car errors))

(let* ((result (check-source-types "(cons 1)"))
       (errors (get-type-errors result)))
  (assert-has-arity-error "cons takes exactly 2 args" 'cons errors))

(let* ((result (check-source-types "(string-ref \"hello\")"))
       (errors (get-type-errors result)))
  (assert-has-arity-error "string-ref takes 2 args" 'string-ref errors))

(let* ((result (check-source-types "(substring \"hello\" 1 2 3)"))
       (errors (get-type-errors result)))
  (assert-has-arity-error "substring takes 3 args" 'substring errors))

(let* ((result (check-source-types "(modulo 10)"))
       (errors (get-type-errors result)))
  (assert-has-arity-error "modulo takes 2 args" 'modulo errors))

;; ===================================================================
;; Test Group: Type Mismatch Errors
;; ===================================================================
(display "Test group: type mismatch errors") (newline)

(let* ((result (check-source-types "(+ \"hello\" 1)"))
       (errors (get-type-errors result)))
  (assert-has-type-error "string arg to +" '+ errors))

(let* ((result (check-source-types "(string-length 42)"))
       (errors (get-type-errors result)))
  (assert-has-type-error "number arg to string-length" 'string-length errors))

(let* ((result (check-source-types "(char-upcase \"a\")"))
       (errors (get-type-errors result)))
  (assert-has-type-error "string arg to char-upcase" 'char-upcase errors))

(let* ((result (check-source-types "(string-append \"hello\" 42)"))
       (errors (get-type-errors result)))
  (assert-has-type-error "number in string-append" 'string-append errors))

(let* ((result (check-source-types "(+ 1 #t)"))
       (errors (get-type-errors result)))
  (assert-has-type-error "bool arg to +" '+ errors))

(let* ((result (check-source-types "(char->integer \"a\")"))
       (errors (get-type-errors result)))
  (assert-has-type-error "string to char->integer" 'char->integer errors))

;; ===================================================================
;; Test Group: Pass 1 - Constraint Inference
;; ===================================================================
(display "Test group: Pass 1 constraint inference") (newline)

(let* ((result (check-source-types
  "(define (f x) (+ x 1) (car x))"))
       (c-errors (get-constraint-errors result)))
  (assert-error-count "contradictory constraints: Number vs Pair" 1 c-errors))

(let* ((result (check-source-types
  "(define (f x) (+ x 1) (- x 2))"))
       (c-errors (get-constraint-errors result)))
  (assert-no-errors "consistent constraints: both Number" c-errors))

(let* ((result (check-source-types
  "(define (g s) (string-length s) (string-append s \"!\"))"))
       (c-errors (get-constraint-errors result)))
  (assert-no-errors "consistent constraints: both String" c-errors))

(let* ((result (check-source-types
  "(define (h x) (string-length x) (+ x 1))"))
       (c-errors (get-constraint-errors result)))
  (assert-error-count "contradictory: String vs Number" 1 c-errors))

;; ===================================================================
;; Test Group: Let-bound types propagate
;; ===================================================================
(display "Test group: let-bound type propagation") (newline)

(let* ((result (check-source-types
  "(let ((x \"hello\")) (+ x 1))"))
       (errors (get-type-errors result)))
  (assert-has-type-error "let-bound string to +" '+ errors))

(let* ((result (check-source-types
  "(let ((x 42)) (+ x 1))"))
       (errors (get-type-errors result)))
  (assert-no-errors "let-bound number to +" errors))

(let* ((result (check-source-types
  "(let* ((x \"hi\") (y (string-length x))) (+ y 1))"))
       (errors (get-type-errors result)))
  (assert-no-errors "let* chain: string-length returns Number" errors))

;; ===================================================================
;; Test Group: Variadic functions
;; ===================================================================
(display "Test group: variadic functions") (newline)

(let* ((result (check-source-types "(+ 1 2 3 4 5)"))
       (errors (get-type-errors result)))
  (assert-no-errors "many args to +" errors))

(let* ((result (check-source-types "(string-append)")))
  (assert-no-errors "zero args to string-append" (get-type-errors result)))

(let* ((result (check-source-types "(list 1 \"a\" #t)")))
  (assert-no-errors "list accepts any args" (get-type-errors result)))

;; ===================================================================
;; Test Group: Quoted data types
;; ===================================================================
(display "Test group: quoted data") (newline)

(let* ((result (check-source-types "(+ 'hello 1)"))
       (errors (get-type-errors result)))
  (assert-has-type-error "quoted symbol to +" '+ errors))

(let* ((result (check-source-types "(string-length '())"))
       (errors (get-type-errors result)))
  (assert-has-type-error "null to string-length" 'string-length errors))

;; ===================================================================
;; Test Group: Higher-order functions
;; ===================================================================
(display "Test group: higher-order functions") (newline)

(let* ((result (check-source-types "(map + (list 1 2 3))"))
       (errors (get-type-errors result)))
  (assert-no-errors "map with + and list" errors))

(let* ((result (check-source-types "(filter odd? (list 1 2 3 4))"))
       (errors (get-type-errors result)))
  (assert-no-errors "filter with odd? and list" errors))

;; ===================================================================
;; Test Group: Complex programs
;; ===================================================================
(display "Test group: complex programs") (newline)

(let* ((result (check-source-types
  "(define (fib n)
     (if (< n 2)
         n
         (+ (fib (- n 1)) (fib (- n 2)))))
   (fib 10)")))
  (assert-no-errors "fibonacci" (get-type-errors result))
  (assert-no-errors "fibonacci constraints" (get-constraint-errors result)))

(let* ((result (check-source-types
  "(define (quicksort lst)
     (if (null? lst)
         '()
         (let ((pivot (car lst))
               (rest (cdr lst)))
           (append
             (quicksort (filter (lambda (x) (< x pivot)) rest))
             (list pivot)
             (quicksort (filter (lambda (x) (>= x pivot)) rest))))))
   (quicksort (list 3 1 4 1 5))")))
  (assert-no-errors "quicksort" (get-type-errors result))
  (assert-no-errors "quicksort constraints" (get-constraint-errors result)))

;; ===================================================================
;; Test Group: Edge cases
;; ===================================================================
(display "Test group: edge cases") (newline)

;; apply - should not error since it's typed loosely
(let* ((result (check-source-types "(apply + (list 1 2 3))")))
  (assert-no-errors "apply with +" (get-type-errors result)))

;; Nested function calls
(let* ((result (check-source-types "(+ (string-length \"hi\") 1)"))
       (errors (get-type-errors result)))
  (assert-no-errors "nested: string-length returns Number to +" errors))

;; Unknown function (not in signatures) - no error
(let* ((result (check-source-types "(define (f x) (f x))")))
  (assert-no-errors "recursive call to user fn" (get-type-errors result)))

;; ===================================================================
;; Summary
;; ===================================================================
(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)

(when (> fail-count 0)
  (exit 1))
