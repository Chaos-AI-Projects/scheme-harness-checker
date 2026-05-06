;; type-signatures.scm
;; Type signatures for whitelisted Scheme functions.
;;
;; Type language:
;;   BaseType  ::= Number | String | Bool | Char | Symbol | Void | Null
;;   Type      ::= BaseType
;;               | (Pair Type Type)
;;               | (List Type)
;;               | (Vector Type)
;;               | (-> Type ... Type)       -- function type (last is return)
;;               | (->* Type Type)          -- variadic: all args of first type, returns second
;;               | (U Type Type ...)        -- union type
;;               | Any                      -- top type
;;
;; Polymorphic type variables: A, B, C (instantiated per call site)
;;
;; Format: (function-name . type-signature)

(
 ;; Arithmetic
 (+ . (->* Number Number))
 (- . (->* Number Number))
 (* . (->* Number Number))
 (/ . (->* Number Number))
 (= . (->* Number Bool))
 (< . (->* Number Bool))
 (> . (->* Number Bool))
 (<= . (->* Number Bool))
 (>= . (->* Number Bool))
 (zero? . (-> Number Bool))
 (positive? . (-> Number Bool))
 (negative? . (-> Number Bool))
 (odd? . (-> Number Bool))
 (even? . (-> Number Bool))
 (abs . (-> Number Number))
 (max . (->* Number Number))
 (min . (->* Number Number))
 (modulo . (-> Number Number Number))
 (remainder . (-> Number Number Number))
 (quotient . (-> Number Number Number))
 (expt . (-> Number Number Number))
 (sqrt . (-> Number Number))
 (floor . (-> Number Number))
 (ceiling . (-> Number Number))
 (round . (-> Number Number))
 (truncate . (-> Number Number))
 (number? . (-> Any Bool))
 (integer? . (-> Any Bool))
 (real? . (-> Any Bool))
 (exact? . (-> Number Bool))
 (inexact? . (-> Number Bool))
 (exact->inexact . (-> Number Number))
 (inexact->exact . (-> Number Number))
 (number->string . (-> Number String))
 (string->number . (-> String (U Number Bool)))

 ;; Boolean
 (not . (-> Any Bool))
 (boolean? . (-> Any Bool))

 ;; Pairs and Lists
 (cons . (-> A B (Pair A B)))
 (car . (-> (Pair A B) A))
 (cdr . (-> (Pair A B) B))
 (caar . (-> (Pair (Pair A Any) Any) A))
 (cadr . (-> (Pair Any (Pair A Any)) A))
 (cdar . (-> (Pair (Pair Any A) Any) A))
 (cddr . (-> (Pair Any (Pair Any A)) A))
 (caaar . (-> Any Any))
 (caadr . (-> Any Any))
 (cadar . (-> Any Any))
 (caddr . (-> Any Any))
 (cdaar . (-> Any Any))
 (cdadr . (-> Any Any))
 (cddar . (-> Any Any))
 (cdddr . (-> Any Any))
 (pair? . (-> Any Bool))
 (null? . (-> Any Bool))
 (list? . (-> Any Bool))
 (list . (->* Any (List Any)))
 (length . (-> (List Any) Number))
 (append . (->* (List Any) (List Any)))
 (reverse . (-> (List Any) (List Any)))
 (map . (-> (-> A B) (List A) (List B)))
 (for-each . (-> (-> A Void) (List A) Void))
 (filter . (-> (-> A Bool) (List A) (List A)))
 (fold-left . (-> (-> B A B) B (List A) B))
 (fold-right . (-> (-> A B B) B (List A) B))
 (assoc . (-> Any (List (Pair Any Any)) (U (Pair Any Any) Bool)))
 (assv . (-> Any (List (Pair Any Any)) (U (Pair Any Any) Bool)))
 (assq . (-> Any (List (Pair Any Any)) (U (Pair Any Any) Bool)))
 (member . (-> Any (List Any) (U (List Any) Bool)))
 (memv . (-> Any (List Any) (U (List Any) Bool)))
 (memq . (-> Any (List Any) (U (List Any) Bool)))

 ;; Symbols
 (symbol? . (-> Any Bool))
 (symbol->string . (-> Symbol String))
 (string->symbol . (-> String Symbol))

 ;; Characters
 (char? . (-> Any Bool))
 (char=? . (->* Char Bool))
 (char<? . (->* Char Bool))
 (char>? . (->* Char Bool))
 (char<=? . (->* Char Bool))
 (char>=? . (->* Char Bool))
 (char-alphabetic? . (-> Char Bool))
 (char-numeric? . (-> Char Bool))
 (char-whitespace? . (-> Char Bool))
 (char-upcase . (-> Char Char))
 (char-downcase . (-> Char Char))
 (char->integer . (-> Char Number))
 (integer->char . (-> Number Char))

 ;; Strings
 (string? . (-> Any Bool))
 (string-length . (-> String Number))
 (string-ref . (-> String Number Char))
 (string=? . (->* String Bool))
 (string<? . (->* String Bool))
 (string>? . (->* String Bool))
 (string<=? . (->* String Bool))
 (string>=? . (->* String Bool))
 (substring . (-> String Number Number String))
 (string-append . (->* String String))
 (string->list . (-> String (List Char)))
 (list->string . (-> (List Char) String))
 (string-copy . (-> String String))
 (string-contains . (-> String String (U Number Bool)))
 (string-upcase . (-> String String))
 (string-downcase . (-> String String))

 ;; Vectors
 (vector? . (-> Any Bool))
 (make-vector . (-> Number Any (Vector Any)))
 (vector . (->* Any (Vector Any)))
 (vector-length . (-> (Vector Any) Number))
 (vector-ref . (-> (Vector Any) Number Any))
 (vector-set! . (-> (Vector Any) Number Any Void))
 (vector->list . (-> (Vector Any) (List Any)))
 (list->vector . (-> (List Any) (Vector Any)))
 (vector-fill! . (-> (Vector Any) Any Void))

 ;; Basic I/O
 (display . (-> Any Void))
 (newline . (-> Void))
 (write . (-> Any Void))
 (format . (->* Any String))

 ;; Control
 (apply . (-> (-> Any Any) (List Any) Any))
 (values . (->* Any Any))
 (call-with-values . (-> (-> Any) (-> Any Any) Any))
 (dynamic-wind . (-> (-> Void) (-> Any) (-> Void) Any))

 ;; Equivalence
 (eq? . (-> Any Any Bool))
 (eqv? . (-> Any Any Bool))
 (equal? . (-> Any Any Bool))

 ;; Type predicates
 (procedure? . (-> Any Bool))
 (eof-object? . (-> Any Bool))
 (port? . (-> Any Bool))
)
