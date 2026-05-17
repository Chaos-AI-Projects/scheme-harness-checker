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
         (param-arities (cadr pass1-result))
         (p1-errors (caddr pass1-result))
         (p2-errors (check-types exprs signatures param-types param-arities)))
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
;; Test Group: Consolidated contradiction errors
;; ===================================================================
(display "Test group: consolidated contradiction errors") (newline)

(let* ((result (check-source-types
  "(define (f x) (+ x 1) (car x) (string-length x))"))
       (c-errors (get-constraint-errors result)))
  (assert-error-count "three-way contradiction emits single error" 1 c-errors))

;; ===================================================================
;; Test Group: User-defined function arity
;; ===================================================================
(display "Test group: user-defined function arity") (newline)

(let* ((result (check-source-types "(define (f x y) (+ x y)) (f 1)"))
       (errors (get-type-errors result)))
  (assert-has-arity-error "user fn too few args" 'f errors))

(let* ((result (check-source-types "(define (f x) (+ x 1)) (f 1 2 3)"))
       (errors (get-type-errors result)))
  (assert-has-arity-error "user fn too many args" 'f errors))

(let* ((result (check-source-types "(define (f x y) (+ x y)) (f 1 2)"))
       (errors (get-type-errors result)))
  (assert-no-errors "user fn correct arity" errors))

(let* ((result (check-source-types "(define (f) 42) (f 1)"))
       (errors (get-type-errors result)))
  (assert-has-arity-error "zero-param fn called with args" 'f errors))

;; ===================================================================
;; Test Group: Body type inference with Pass 1 constraints
;; ===================================================================
(display "Test group: body type inference") (newline)

;; x is constrained to Number by +, y is bound to x (Number),
;; so string-length on y is a type error
(let* ((result (check-source-types
  "(define (f x) (+ x 1) (let ((y x)) (string-length y)))"))
       (errors (get-type-errors result)))
  (assert-has-type-error "body inference catches let-bound constraint violation"
    'string-length errors))

;; Verify that body inference doesn't produce false positives
(let* ((result (check-source-types
  "(define (f x) (+ x 1) (let ((y x)) (* y 2)))"))
       (errors (get-type-errors result)))
  (assert-no-errors "body inference no false positive" errors))

;; ===================================================================
;; Test Group: Record Types
;; ===================================================================
(display "Test group: record types") (newline)

;; --- Construction and predicates ---
(let ((r (make-type-record '((name . #(base String)) (age . #(base Number)))
                           '(name age))))
  (assert-true "type-record? on record" (type-record? r))
  (assert-true "type-record? false on base" (not (type-record? type:number)))
  (assert-equal "record-fields length" 2 (length (type-record-fields r)))
  (assert-equal "record-required" '(name age) (type-record-required r)))

;; --- record-field-type ---
(let ((r (make-type-record (list (cons 'x type:number) (cons 'y type:string))
                           '(x))))
  (assert-true "record-field-type existing field"
    (type=? (record-field-type r 'x) type:number))
  (assert-true "record-field-type second field"
    (type=? (record-field-type r 'y) type:string))
  (assert-equal "record-field-type missing field" #f (record-field-type r 'z)))

;; --- type=? for records ---
(let ((r1 (make-type-record (list (cons 'a type:number) (cons 'b type:string))
                            '(a)))
      (r2 (make-type-record (list (cons 'b type:string) (cons 'a type:number))
                            '(a)))
      (r3 (make-type-record (list (cons 'a type:number) (cons 'b type:string))
                            '(a b))))
  (assert-true "type=? records same fields different order" (type=? r1 r2))
  (assert-true "type=? records different required" (not (type=? r1 r3))))

;; --- Subtype: width subtyping ---
(let ((wider (make-type-record
               (list (cons 'x type:number) (cons 'y type:string) (cons 'z type:bool))
               '(x y z)))
      (narrower (make-type-record
                  (list (cons 'x type:number) (cons 'y type:string))
                  '(x y))))
  (assert-true "wider record is subtype of narrower"
    (subtype? wider narrower))
  (assert-true "narrower record is NOT subtype of wider"
    (not (subtype? narrower wider))))

;; --- Subtype: covariant field types ---
(let ((sub (make-type-record
             (list (cons 'items (make-type-list type:number)))
             '(items)))
      (sup (make-type-record
             (list (cons 'items (make-type-list type:any)))
             '(items))))
  (assert-true "record subtype with covariant field"
    (subtype? sub sup))
  (assert-true "record not subtype with contravariant field"
    (not (subtype? sup sub))))

;; --- Subtype: required field compatibility ---
(let ((r-required (make-type-record
                    (list (cons 'x type:number))
                    '(x)))
      (r-optional (make-type-record
                    (list (cons 'x type:number))
                    '())))
  ;; A record where x is required is a subtype of one where x is optional
  (assert-true "required field subtype of optional"
    (subtype? r-required r-optional))
  ;; But not vice versa: optional cannot satisfy required
  (assert-true "optional field NOT subtype of required"
    (not (subtype? r-optional r-required))))

;; --- Record subtype of Any ---
(let ((r (make-type-record (list (cons 'a type:number)) '(a))))
  (assert-true "record subtype of Any" (subtype? r type:any)))

;; --- type->string for records ---
(let ((r (make-type-record (list (cons 'name type:string) (cons 'age type:number))
                           '(name))))
  (assert-equal "type->string record"
    "(Record (name: String) (age?: Number))"
    (type->string r)))

;; --- parse-type-sexpr for records ---
(let ((r (parse-type-sexpr '(Record ((name String) (age Number)) (name)))))
  (assert-true "parse record type is record" (type-record? r))
  (assert-true "parse record field name type"
    (type=? (record-field-type r 'name) type:string))
  (assert-true "parse record field age type"
    (type=? (record-field-type r 'age) type:number))
  (assert-equal "parse record required" '(name) (type-record-required r)))

(let ((r (parse-type-sexpr '(Record ((items (List Number)))))))
  (assert-true "parse record without required" (type-record? r))
  (assert-equal "parse record empty required" '() (type-record-required r))
  (assert-true "parse record nested type"
    (type=? (record-field-type r 'items) (make-type-list type:number))))

;; --- Union with records (point 4: keep as separate members) ---
(let* ((r1 (make-type-record (list (cons 'x type:number)) '(x)))
       (r2 (make-type-record (list (cons 'y type:string)) '(y)))
       (u (simplify-union (list r1 r2))))
  (assert-true "union of different records stays union"
    (type-union? u))
  (assert-equal "union of different records has 2 members"
    2 (length (type-union-members u))))

;; Identical records in union collapse
(let* ((r1 (make-type-record (list (cons 'x type:number)) '(x)))
       (r2 (make-type-record (list (cons 'x type:number)) '(x)))
       (u (simplify-union (list r1 r2))))
  (assert-true "union of identical records collapses"
    (type-record? u)))

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
