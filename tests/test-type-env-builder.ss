;; test-type-env-builder.ss
;; Tests for the type-env builder module.
;;
;; Run with: scheme --libdirs ../src --program test-type-env-builder.ss

(import (rnrs)
        (harness-checker type-env-builder)
        (harness-checker types)
        (harness-checker termination)
        (harness-checker whitelist-checker))  ;; for read-all-expressions

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

(define (assert-false test-name value)
  (assert-equal test-name #f value))

;; Helper: look up a parameter type for a function from the per-function param-types
(define (param-type-lookup param-types fn-name param-name)
  (let ((fn-entry (assq fn-name param-types)))
    (and fn-entry
         (let ((param-entry (assq param-name (cdr fn-entry))))
           (and param-entry (cdr param-entry))))))

;; ============================================================
;; Test Group: Empty inputs
;; ============================================================
(display "=== build-type-env: empty inputs ===") (newline)

(let ((env (build-type-env '() '() '())))
  (assert-equal "empty inputs produce empty param-types" '() env))

;; ============================================================
;; Test Group: Signatures only (no pass1, no defines)
;; ============================================================
(display "=== build-type-env: signatures only (no defines) ===") (newline)

(let* ((sigs (list (cons 'car (make-type-fn (list (make-type-pair type:any type:any)) type:any))
                   (cons '+ (make-type-fn-variadic type:number type:number))))
       (env (build-type-env '() sigs '())))
  ;; No defines in source, so no per-function entries
  (assert-equal "no defines: empty param-types" '() env))

;; ============================================================
;; Test Group: Signature-derived parameter types
;; ============================================================
(display "=== build-type-env: signature-derived params ===") (newline)

;; (define (sum-list lst) ...) with signature (sum-list . (-> (List Number) Number))
(let* ((exprs (read-all-expressions
                "(define (sum-list lst) (if (null? lst) 0 (+ (car lst) (sum-list (cdr lst)))))"))
       (sigs (list (cons 'sum-list (make-type-fn (list (make-type-list type:number)) type:number))))
       (pt (build-type-env exprs sigs '())))
  (let ((lst-type (param-type-lookup pt 'sum-list 'lst)))
    (assert-true "signature-derived: lst has List type"
      (and lst-type (type-list? lst-type)))
    (assert-true "signature-derived: lst element is Number"
      (and lst-type (type=? type:number (type-list-elem lst-type))))))

;; Multiple parameters
(let* ((exprs (read-all-expressions
                "(define (add a b) (+ a b))"))
       (sigs (list (cons 'add (make-type-fn (list type:number type:number) type:number))))
       (pt (build-type-env exprs sigs '())))
  (assert-true "signature-derived: a is Number"
    (type=? type:number (param-type-lookup pt 'add 'a)))
  (assert-true "signature-derived: b is Number"
    (type=? type:number (param-type-lookup pt 'add 'b))))

;; Signature with type variables should be skipped (no useful info)
(let* ((exprs (read-all-expressions "(define (id x) x)"))
       (sigs (list (cons 'id (make-type-fn (list (make-type-var 'A)) (make-type-var 'A)))))
       (pt (build-type-env exprs sigs '())))
  (let ((x-entry (param-type-lookup pt 'id 'x)))
    ;; x should not have a type-var entry (filtered out)
    (assert-true "type-var params not added to param-types"
      (or (not x-entry) (not (type-var? x-entry))))))

;; define-lambda form: (define f (lambda (x) ...))
(let* ((exprs (read-all-expressions "(define f (lambda (n) (- n 1)))"))
       (sigs (list (cons 'f (make-type-fn (list type:number) type:number))))
       (pt (build-type-env exprs sigs '())))
  (assert-true "define-lambda: n is Number"
    (type=? type:number (param-type-lookup pt 'f 'n))))

;; ============================================================
;; Test Group: Pass 1 inferred types
;; ============================================================
(display "=== build-type-env: pass1 inferred types ===") (newline)

;; Pass 1 produces: ((fn-name . ((param . type) ...)) ...)
;; build-type-env needs defines to match against, so provide exprs
(let* ((exprs (read-all-expressions "(define (my-func x y) (+ x y))"))
       (param-types (list (cons 'my-func
                                (list (cons 'x type:number)
                                      (cons 'y type:string)))))
       (pt (build-type-env exprs '() param-types)))
  (assert-true "pass1: x is Number"
    (type=? type:number (param-type-lookup pt 'my-func 'x)))
  (assert-true "pass1: y is String"
    (type=? type:string (param-type-lookup pt 'my-func 'y))))

;; Pass 1 with Any types should be filtered out
(let* ((exprs (read-all-expressions "(define (f a b) (+ a b))"))
       (param-types (list (cons 'f
                                (list (cons 'a type:number)
                                      (cons 'b type:any)))))
       (pt (build-type-env exprs '() param-types)))
  (assert-true "pass1: a is Number"
    (type=? type:number (param-type-lookup pt 'f 'a)))
  (assert-false "pass1: Any-typed b not in param-types"
    (param-type-lookup pt 'f 'b)))

;; ============================================================
;; Test Group: Priority — Pass 1 overrides signature-derived
;; ============================================================
(display "=== build-type-env: merge priority ===") (newline)

;; Signature says x is Number, Pass 1 says x is (List Number)
;; Pass 1 should win (more specific, derived from actual usage)
(let* ((exprs (read-all-expressions "(define (f x) x)"))
       (sigs (list (cons 'f (make-type-fn (list type:number) type:number))))
       (param-types (list (cons 'f (list (cons 'x (make-type-list type:number))))))
       (pt (build-type-env exprs sigs param-types)))
  (assert-true "pass1 type wins over signature-derived"
    (type-list? (param-type-lookup pt 'f 'x))))

;; ============================================================
;; Test Group: Multiple functions — per-function scoping
;; ============================================================
(display "=== build-type-env: multiple functions (scoped) ===") (newline)

(let* ((exprs (read-all-expressions
                (string-append
                  "(define (sum lst) (if (null? lst) 0 (+ (car lst) (sum (cdr lst))))) "
                  "(define (len lst) (if (null? lst) 0 (+ 1 (len (cdr lst)))))")))
       (sigs (list (cons 'sum (make-type-fn (list (make-type-list type:number)) type:number))
                   (cons 'len (make-type-fn (list (make-type-list type:any)) type:number))))
       (pt (build-type-env exprs sigs '())))
  ;; Each function should have its own entry for 'lst'
  (assert-true "sum: lst has List type"
    (type-list? (param-type-lookup pt 'sum 'lst)))
  (assert-true "len: lst has List type"
    (type-list? (param-type-lookup pt 'len 'lst)))
  ;; Verify they have DIFFERENT element types (sum has Number, len has Any which is filtered)
  (assert-true "sum: lst element is Number"
    (type=? type:number (type-list-elem (param-type-lookup pt 'sum 'lst)))))

;; ============================================================
;; Test Group: Scoping — two functions, same param name, different types
;; ============================================================
(display "=== build-type-env: scoping test ===") (newline)

;; This is the key test from the plan: two functions with same-named parameter
;; but different types. With per-function scoping, each gets its own binding.
(let* ((node-type (make-type-record
                    (list (cons 'value type:number)
                          (cons 'next (make-type-union (list type:any type:null))))
                    '(value next)))
       (exprs (read-all-expressions
                (string-append
                  "(define (sum-list xs) (if (null? xs) 0 (+ (car xs) (sum-list (cdr xs))))) "
                  "(define (walk-nodes xs) (if (null? xs) 0 (+ (node-value xs) (walk-nodes (node-next xs)))))")))
       (sigs (list (cons 'sum-list (make-type-fn (list (make-type-list type:number)) type:number))
                   (cons 'walk-nodes (make-type-fn (list node-type) type:number))))
       (pt (build-type-env exprs sigs '())))
  ;; sum-list's xs should be (List Number)
  (let ((sum-xs (param-type-lookup pt 'sum-list 'xs)))
    (assert-true "scoping: sum-list xs is List"
      (and sum-xs (type-list? sum-xs)))
    (assert-true "scoping: sum-list xs element is Number"
      (and sum-xs (type=? type:number (type-list-elem sum-xs)))))
  ;; walk-nodes's xs should be the record type
  (let ((walk-xs (param-type-lookup pt 'walk-nodes 'xs)))
    (assert-true "scoping: walk-nodes xs is Record"
      (and walk-xs (type-record? walk-xs))))
  ;; Integration: check-termination with scoped param-types resolves both correctly
  (let* ((type-env sigs)
         (violations (check-termination exprs type-env pt)))
    (assert-equal "scoping: both functions terminate with correct scoped types"
      0 (length violations))))

;; ============================================================
;; Test Group: Integration — type-env enables termination proof
;; ============================================================
(display "=== build-type-env: integration with termination ===") (newline)

;; Record traversal: without type-env, (node-next n) is not recognized as
;; decreasing. With signature-derived type-env, the record field resolves.
(let* ((node-type (make-type-record
                    (list (cons 'value type:number)
                          (cons 'next (make-type-union (list type:any type:null))))
                    '(value next)))
       (source "(define (my-walk n) (if (null? n) 0 (+ (node-value n) (my-walk (node-next n)))))")
       (exprs (read-all-expressions source))
       (sigs (list (cons 'my-walk (make-type-fn (list node-type) type:number))))
       (pt (build-type-env exprs sigs '()))
       (violations-with-env (check-termination exprs sigs pt))
       (violations-without-env (check-termination exprs '())))
  ;; Without type-env, the checker flags (node-next n) as not decreasing.
  (assert-equal "without type-env: violation expected" 1 (length violations-without-env))
  ;; With type-env from signatures, n's record type resolves the accessor.
  (assert-equal "with signature-derived type-env: no violations" 0 (length violations-with-env)))

;; Record traversal via signature
(let* ((node-type (make-type-record
                    (list (cons 'value type:number)
                          (cons 'next (make-type-union (list type:any type:null))))
                    '(value next)))
       (source "(define (walk n) (if (null? n) 0 (+ (node-value n) (walk (node-next n)))))")
       (exprs (read-all-expressions source))
       (sigs (list (cons 'walk (make-type-fn (list node-type) type:number))))
       (pt (build-type-env exprs sigs '()))
       (violations (check-termination exprs sigs pt)))
  (assert-equal "record traversal via signature-derived type-env: no violations"
    0 (length violations)))

;; Variadic function signature
(let* ((source "(define (sum-all . nums) (if (null? nums) 0 (+ (car nums) (apply sum-all (cdr nums)))))")
       (exprs (read-all-expressions source))
       (sigs (list (cons 'sum-all (make-type-fn-variadic type:number type:number))))
       (pt (build-type-env exprs sigs '()))
       (nums-type (param-type-lookup pt 'sum-all 'nums)))
  (assert-true "variadic: nums has Number type from signature"
    (and nums-type (type=? type:number nums-type))))

;; ============================================================
;; Test Group: No signature match — graceful fallback
;; ============================================================
(display "=== build-type-env: no signature match ===") (newline)

(let* ((exprs (read-all-expressions "(define (unknown-fn x y) (+ x y))"))
       (pt (build-type-env exprs '() '())))
  (assert-false "no signatures: unknown-fn not in param-types"
    (assq 'unknown-fn pt)))

;; ============================================================
;; Test Group: begin-wrapped defines
;; ============================================================
(display "=== build-type-env: begin-wrapped defines ===") (newline)

(let* ((exprs (read-all-expressions
                "(begin (define (f x) (+ x 1)) (define (g y) (* y 2)))"))
       (sigs (list (cons 'f (make-type-fn (list type:number) type:number))
                   (cons 'g (make-type-fn (list type:number) type:number))))
       (pt (build-type-env exprs sigs '())))
  (assert-true "begin-wrapped: f's x is Number"
    (type=? type:number (param-type-lookup pt 'f 'x)))
  (assert-true "begin-wrapped: g's y is Number"
    (type=? type:number (param-type-lookup pt 'g 'y))))

;; ============================================================
;; Test Group: Named-let inherits enclosing function's scoped type-env
;; ============================================================
(display "=== build-type-env: named-let scoping ===") (newline)

;; Named-let inside a function should see the function's parameter types
;; via the scoped type-env passed through analyze-named-let-forms.
;; The named-let variable reuses the parameter name (common pattern),
;; so type-env-lookup finds the type from the enclosing function's scope.
(let* ((node-type (make-type-record
                    (list (cons 'value type:number)
                          (cons 'next (make-type-union (list type:any type:null))))
                    '(value next)))
       (source "(define (traverse n) (let loop ((n n)) (if (null? n) 0 (+ (node-value n) (loop (node-next n))))))")
       (exprs (read-all-expressions source))
       (sigs (list (cons 'traverse (make-type-fn (list node-type) type:number))))
       (pt (build-type-env exprs sigs '()))
       ;; Named-let 'loop' uses (node-next n) which requires knowing n's type.
       ;; With per-function scoping, analyze-named-let-forms sees traverse's
       ;; param types including (n . record-type).
       (violations (check-termination exprs sigs pt)))
  (assert-equal "named-let inherits enclosing function's scoped type-env: no violations"
    0 (length violations)))

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
