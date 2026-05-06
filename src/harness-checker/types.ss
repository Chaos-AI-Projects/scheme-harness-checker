;; types.ss
;; Type representation for the static type checker.
;;
;; Provides type constructors, predicates, accessors, subtype checking,
;; and union simplification for the harness-checker type system.

(library (harness-checker types)
  (export ;; Type constructors
          make-type-base make-type-pair make-type-list make-type-vector
          make-type-fn make-type-fn-variadic make-type-union make-type-any
          make-type-var
          ;; Type predicates
          type-base? type-pair? type-list? type-vector?
          type-fn? type-fn-variadic? type-union? type-any? type-var?
          ;; Type accessors
          type-base-name
          type-pair-car type-pair-cdr
          type-list-elem
          type-vector-elem
          type-fn-params type-fn-return
          type-fn-variadic-param type-fn-variadic-return
          type-fn-variadic-min-arity
          type-union-members
          type-var-name
          ;; Operations
          subtype?
          type=?
          type->string
          simplify-union
          ;; Well-known types
          type:number type:string type:bool type:char
          type:symbol type:void type:null type:any
          ;; Signature loading
          load-type-signatures
          parse-type-signature)
  (import (rnrs))

  ;; ---------------------------------------------------------------
  ;; Type representation using tagged vectors
  ;; ---------------------------------------------------------------
  ;; Each type is a vector: #(tag field1 field2 ...)

  ;; Base types: Number, String, Bool, Char, Symbol, Void, Null
  (define (make-type-base name) (vector 'base name))
  (define (type-base? t) (and (vector? t) (eq? (vector-ref t 0) 'base)))
  (define (type-base-name t) (vector-ref t 1))

  ;; Pair type: (Pair car-type cdr-type)
  (define (make-type-pair car-t cdr-t) (vector 'pair car-t cdr-t))
  (define (type-pair? t) (and (vector? t) (eq? (vector-ref t 0) 'pair)))
  (define (type-pair-car t) (vector-ref t 1))
  (define (type-pair-cdr t) (vector-ref t 2))

  ;; List type: (List elem-type)
  (define (make-type-list elem-t) (vector 'list elem-t))
  (define (type-list? t) (and (vector? t) (eq? (vector-ref t 0) 'list)))
  (define (type-list-elem t) (vector-ref t 1))

  ;; Vector type: (Vector elem-type)
  (define (make-type-vector elem-t) (vector 'vector elem-t))
  (define (type-vector? t) (and (vector? t) (eq? (vector-ref t 0) 'vector)))
  (define (type-vector-elem t) (vector-ref t 1))

  ;; Function type: (-> param-types ... return-type)
  (define (make-type-fn params return) (vector 'fn params return))
  (define (type-fn? t) (and (vector? t) (eq? (vector-ref t 0) 'fn)))
  (define (type-fn-params t) (vector-ref t 1))
  (define (type-fn-return t) (vector-ref t 2))

  ;; Variadic function type: (->* param-type return-type)
  ;; All arguments must be param-type, min-arity defaults to 0
  (define make-type-fn-variadic
    (case-lambda
      ((param-t return-t) (vector 'fn-var param-t return-t 0))
      ((param-t return-t min-arity) (vector 'fn-var param-t return-t min-arity))))
  (define (type-fn-variadic? t) (and (vector? t) (eq? (vector-ref t 0) 'fn-var)))
  (define (type-fn-variadic-param t) (vector-ref t 1))
  (define (type-fn-variadic-return t) (vector-ref t 2))
  (define (type-fn-variadic-min-arity t) (vector-ref t 3))

  ;; Union type: (U type1 type2 ...)
  (define (make-type-union members) (vector 'union members))
  (define (type-union? t) (and (vector? t) (eq? (vector-ref t 0) 'union)))
  (define (type-union-members t) (vector-ref t 1))

  ;; Any type (top)
  (define (make-type-any) (vector 'any))
  (define (type-any? t) (and (vector? t) (eq? (vector-ref t 0) 'any)))

  ;; Type variable (for polymorphic signatures)
  (define (make-type-var name) (vector 'tvar name))
  (define (type-var? t) (and (vector? t) (eq? (vector-ref t 0) 'tvar)))
  (define (type-var-name t) (vector-ref t 1))

  ;; ---------------------------------------------------------------
  ;; Well-known type constants
  ;; ---------------------------------------------------------------
  (define type:number (make-type-base 'Number))
  (define type:string (make-type-base 'String))
  (define type:bool   (make-type-base 'Bool))
  (define type:char   (make-type-base 'Char))
  (define type:symbol (make-type-base 'Symbol))
  (define type:void   (make-type-base 'Void))
  (define type:null   (make-type-base 'Null))
  (define type:any    (make-type-any))

  ;; ---------------------------------------------------------------
  ;; Type equality
  ;; ---------------------------------------------------------------
  (define (type=? a b)
    (cond
      ((and (type-any? a) (type-any? b)) #t)
      ((and (type-base? a) (type-base? b))
       (eq? (type-base-name a) (type-base-name b)))
      ((and (type-var? a) (type-var? b))
       (eq? (type-var-name a) (type-var-name b)))
      ((and (type-pair? a) (type-pair? b))
       (and (type=? (type-pair-car a) (type-pair-car b))
            (type=? (type-pair-cdr a) (type-pair-cdr b))))
      ((and (type-list? a) (type-list? b))
       (type=? (type-list-elem a) (type-list-elem b)))
      ((and (type-vector? a) (type-vector? b))
       (type=? (type-vector-elem a) (type-vector-elem b)))
      ((and (type-fn? a) (type-fn? b))
       (and (= (length (type-fn-params a)) (length (type-fn-params b)))
            (for-all type=? (type-fn-params a) (type-fn-params b))
            (type=? (type-fn-return a) (type-fn-return b))))
      ((and (type-fn-variadic? a) (type-fn-variadic? b))
       (and (type=? (type-fn-variadic-param a) (type-fn-variadic-param b))
            (type=? (type-fn-variadic-return a) (type-fn-variadic-return b))))
      ((and (type-union? a) (type-union? b))
       (let ((ma (type-union-members a))
             (mb (type-union-members b)))
         (and (= (length ma) (length mb))
              (for-all (lambda (t) (exists (lambda (u) (type=? t u)) mb)) ma))))
      (else #f)))

  ;; ---------------------------------------------------------------
  ;; Subtype checking
  ;; ---------------------------------------------------------------
  ;; Returns #t if type `a` is a subtype of type `b`.
  (define (subtype? a b)
    (cond
      ;; Any is the top type — everything is a subtype of Any
      ((type-any? b) #t)
      ;; Type variables in signatures accept anything
      ((type-var? b) #t)
      ;; Type vars on left are compatible with anything
      ((type-var? a) #t)
      ;; Any is a subtype of nothing except Any/type-var (handled above)
      ((type-any? a) #f)
      ;; Equal types
      ((type=? a b) #t)
      ;; Null is a subtype of any List
      ((and (type-base? a) (eq? (type-base-name a) 'Null) (type-list? b)) #t)
      ;; List covariance
      ((and (type-list? a) (type-list? b))
       (subtype? (type-list-elem a) (type-list-elem b)))
      ;; Pair covariance
      ((and (type-pair? a) (type-pair? b))
       (and (subtype? (type-pair-car a) (type-pair-car b))
            (subtype? (type-pair-cdr a) (type-pair-cdr b))))
      ;; Vector covariance
      ((and (type-vector? a) (type-vector? b))
       (subtype? (type-vector-elem a) (type-vector-elem b)))
      ;; A type is a subtype of a union if it's a subtype of any member
      ((type-union? b)
       (exists (lambda (m) (subtype? a m)) (type-union-members b)))
      ;; A union is a subtype of T if all its members are subtypes of T
      ((type-union? a)
       (for-all (lambda (m) (subtype? m b)) (type-union-members a)))
      ;; List is a subtype of Pair (non-empty list)
      ((and (type-list? a) (type-pair? b))
       (and (subtype? (type-list-elem a) (type-pair-car b))
            (subtype? a (type-pair-cdr b))))
      ;; Function subtyping: fn-variadic is subtype of fn when param types match
      ((and (type-fn-variadic? a) (type-fn? b))
       (and (for-all (lambda (p) (subtype? (type-fn-variadic-param a) p))
                     (type-fn-params b))
            (subtype? (type-fn-variadic-return a) (type-fn-return b))))
      ;; Fixed-arity fn is subtype of fn (contravariant params, covariant return)
      ((and (type-fn? a) (type-fn? b))
       (or (for-all type-var? (type-fn-params b))  ;; target has type vars = accept
           (and (= (length (type-fn-params a)) (length (type-fn-params b)))
                (for-all subtype? (type-fn-params b) (type-fn-params a))
                (subtype? (type-fn-return a) (type-fn-return b)))))
      (else #f)))

  ;; ---------------------------------------------------------------
  ;; Union simplification
  ;; ---------------------------------------------------------------
  (define (simplify-union types)
    (let ((unique (fold-left
                   (lambda (acc t)
                     (if (exists (lambda (u) (type=? t u)) acc)
                         acc
                         (cons t acc)))
                   '()
                   types)))
      (cond
        ((null? unique) type:void)
        ((null? (cdr unique)) (car unique))
        (else (make-type-union (reverse unique))))))

  ;; ---------------------------------------------------------------
  ;; Type display
  ;; ---------------------------------------------------------------
  (define (type->string t)
    (cond
      ((type-any? t) "Any")
      ((type-base? t) (symbol->string (type-base-name t)))
      ((type-var? t) (symbol->string (type-var-name t)))
      ((type-pair? t)
       (string-append "(Pair " (type->string (type-pair-car t))
                      " " (type->string (type-pair-cdr t)) ")"))
      ((type-list? t)
       (string-append "(List " (type->string (type-list-elem t)) ")"))
      ((type-vector? t)
       (string-append "(Vector " (type->string (type-vector-elem t)) ")"))
      ((type-fn? t)
       (string-append "(-> "
                      (fold-left (lambda (acc p)
                                   (string-append acc (type->string p) " "))
                                 "" (type-fn-params t))
                      (type->string (type-fn-return t)) ")"))
      ((type-fn-variadic? t)
       (string-append "(->* " (type->string (type-fn-variadic-param t))
                      " " (type->string (type-fn-variadic-return t)) ")"))
      ((type-union? t)
       (string-append "(U "
                      (fold-left (lambda (acc m)
                                   (if (string=? acc "")
                                       (type->string m)
                                       (string-append acc " " (type->string m))))
                                 "" (type-union-members t))
                      ")"))
      (else "?")))

  ;; ---------------------------------------------------------------
  ;; Signature file parsing
  ;; ---------------------------------------------------------------

  ;; Parse a type s-expression into an internal type representation
  (define (parse-type-sexpr sexpr)
    (cond
      ((symbol? sexpr)
       (case sexpr
         ((Number) type:number)
         ((String) type:string)
         ((Bool) type:bool)
         ((Char) type:char)
         ((Symbol) type:symbol)
         ((Void) type:void)
         ((Null) type:null)
         ((Any) type:any)
         (else (make-type-var sexpr))))  ;; A, B, C etc.
      ((pair? sexpr)
       (let ((head (car sexpr)))
         (case head
           ((Pair)
            (make-type-pair (parse-type-sexpr (cadr sexpr))
                            (parse-type-sexpr (caddr sexpr))))
           ((List)
            (make-type-list (parse-type-sexpr (cadr sexpr))))
           ((Vector)
            (make-type-vector (parse-type-sexpr (cadr sexpr))))
           ((->)
            (let* ((parts (cdr sexpr))
                   (params (let loop ((p parts))
                             (if (null? (cdr p))
                                 '()
                                 (cons (parse-type-sexpr (car p))
                                       (loop (cdr p))))))
                   (return-type (parse-type-sexpr (car (last-pair parts)))))
              (make-type-fn params return-type)))
           ((->*)
            (make-type-fn-variadic (parse-type-sexpr (cadr sexpr))
                                   (parse-type-sexpr (caddr sexpr))))
           ((U)
            (make-type-union (map parse-type-sexpr (cdr sexpr))))
           (else type:any))))
      (else type:any)))

  ;; Helper: get last pair of a list
  (define (last-pair lst)
    (if (null? (cdr lst))
        lst
        (last-pair (cdr lst))))

  ;; Parse a single signature entry: (name . type-sexpr)
  (define (parse-type-signature entry)
    (cons (car entry) (parse-type-sexpr (cdr entry))))

  ;; Load type signatures from a file.
  ;; Returns an alist of (symbol . type).
  (define (load-type-signatures path)
    (let* ((port (open-input-file path))
           (data (read port)))
      (close-port port)
      (map parse-type-signature data)))
)
