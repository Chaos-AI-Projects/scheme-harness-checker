;; json-schema.ss
;; JSON Schema to internal type translation.
;;
;; Parses a JSON Schema (as produced by json-read from (chaos json)) and
;; converts it directly into the harness-checker type representation.
;;
;; Supports the static JSON Schema subset:
;;   type, properties, required, items, enum, oneOf, anyOf, allOf
;;
;; Out of scope (ignored if encountered):
;;   patternProperties, additionalProperties, if/then/else, $ref, $defs

(library (harness-checker json-schema)
  (export json-schema->type json-object?)
  (import (rnrs)
          (harness-checker types))

  ;; ---------------------------------------------------------------
  ;; JSON object helpers
  ;; ---------------------------------------------------------------
  ;; json-read produces objects as vectors of (string . value) pairs.

  ;; Look up a string key in a JSON object vector.
  ;; Returns the value or default if not found.
  (define (json-object-ref obj key default)
    (let loop ((i 0))
      (if (>= i (vector-length obj))
          default
          (let ((entry (vector-ref obj i)))
            (if (string=? (car entry) key)
                (cdr entry)
                (loop (+ i 1)))))))

  ;; Check if a JSON value is an object (vector of pairs).
  (define (json-object? v)
    (and (vector? v)
         (or (= (vector-length v) 0)
             (pair? (vector-ref v 0)))))

  ;; ---------------------------------------------------------------
  ;; Main translation: JSON Schema (parsed JSON) -> internal type
  ;; ---------------------------------------------------------------

  ;; Convert a parsed JSON Schema value to an internal type.
  ;; schema is the output of json-read: vectors for objects, lists for arrays,
  ;; strings for strings, numbers for numbers, booleans, or json-null.
  (define (json-schema->type schema)
    (cond
      ;; Empty schema or non-object -> Any
      ((not (json-object? schema)) type:any)
      ((= (vector-length schema) 0) type:any)

      ;; Check for combinators first (they take precedence)
      (else
       (let ((any-of (json-object-ref schema "anyOf" #f))
             (one-of (json-object-ref schema "oneOf" #f))
             (all-of (json-object-ref schema "allOf" #f))
             (enum-val (json-object-ref schema "enum" #f))
             (type-val (json-object-ref schema "type" #f)))
         (cond
           ;; anyOf / oneOf -> union of member types
           (any-of (translate-union any-of))
           (one-of (translate-union one-of))

           ;; allOf -> merge record fields if all are objects, else Any
           (all-of (translate-all-of all-of))

           ;; enum -> common base type of the enum values
           (enum-val (translate-enum enum-val))

           ;; type keyword present
           (type-val (translate-typed schema type-val))

           ;; No type keyword -> Any
           (else type:any))))))

  ;; ---------------------------------------------------------------
  ;; Translate a schema with a "type" keyword
  ;; ---------------------------------------------------------------
  (define (translate-typed schema type-val)
    (cond
      ;; JSON Schema allows "type": ["string", "null"] for nullable fields;
      ;; fall back to Any for array type values
      ((not (string? type-val)) type:any)
      ((string=? type-val "string")  type:string)
      ((string=? type-val "number")  type:number)
      ((string=? type-val "integer") type:number)
      ((string=? type-val "boolean") type:bool)
      ((string=? type-val "null")    type:null)
      ((string=? type-val "object")  (translate-object schema))
      ((string=? type-val "array")   (translate-array schema))
      (else type:any)))

  ;; ---------------------------------------------------------------
  ;; Translate an object schema -> Record type
  ;; ---------------------------------------------------------------
  (define (translate-object schema)
    (let ((props (json-object-ref schema "properties" #f))
          (req   (json-object-ref schema "required" #f)))
      (if (not props)
          ;; Object without properties -> empty record
          (make-type-record '() '())
          ;; Object with properties -> Record with field types
          (let* ((fields (translate-properties props))
                 (required (if (and req (list? req))
                               (map string->symbol req)
                               '())))
            (make-type-record fields required)))))

  ;; Translate a "properties" JSON object into an alist of (symbol . type).
  (define (translate-properties props)
    (let loop ((i 0) (acc '()))
      (if (>= i (vector-length props))
          (reverse acc)
          (let* ((entry (vector-ref props i))
                 (name (string->symbol (car entry)))
                 (sub-schema (cdr entry))
                 (field-type (json-schema->type sub-schema)))
            (loop (+ i 1) (cons (cons name field-type) acc))))))

  ;; ---------------------------------------------------------------
  ;; Translate an array schema -> List type
  ;; ---------------------------------------------------------------
  (define (translate-array schema)
    (let ((items (json-object-ref schema "items" #f)))
      (if items
          (make-type-list (json-schema->type items))
          (make-type-list type:any))))

  ;; ---------------------------------------------------------------
  ;; Translate anyOf / oneOf -> Union type
  ;; ---------------------------------------------------------------
  (define (translate-union schemas)
    (if (and (list? schemas) (not (null? schemas)))
        (simplify-union (map json-schema->type schemas))
        type:any))

  ;; ---------------------------------------------------------------
  ;; Translate allOf -> merge record fields
  ;; ---------------------------------------------------------------
  ;; If all members are object types (Records), merge their fields.
  ;; The stricter type wins per field. If any member is not an object,
  ;; fall back to Any.
  (define (translate-all-of schemas)
    (if (not (and (list? schemas) (not (null? schemas))))
        type:any
        (let ((types (map json-schema->type schemas)))
          (if (for-all type-record? types)
              (merge-records types)
              type:any))))

  ;; Merge multiple record types by combining their fields.
  ;; For duplicate fields, pick the more specific (non-Any) type.
  ;; A field is required if it is required in any member record.
  (define (merge-records records)
    (let loop ((remaining records)
               (merged-fields '())
               (merged-required '()))
      (if (null? remaining)
          (make-type-record merged-fields merged-required)
          (let* ((rec (car remaining))
                 (fields (type-record-fields rec))
                 (req (type-record-required rec))
                 ;; Merge fields
                 (new-fields (merge-field-lists merged-fields fields))
                 ;; Union of required lists (deduplicated)
                 (new-required (fold-left
                                (lambda (acc r)
                                  (if (memq r acc) acc (cons r acc)))
                                merged-required
                                req)))
            (loop (cdr remaining) new-fields new-required)))))

  ;; Merge two field alists. For duplicate keys, pick the more specific type.
  (define (merge-field-lists base new-fields)
    (fold-left
     (lambda (acc field)
       (let ((name (car field))
             (ftype (cdr field)))
         (let ((existing (assq name acc)))
           (if existing
               ;; Duplicate: pick more specific (non-Any) type
               (map (lambda (f)
                      (if (eq? (car f) name)
                          (cons name (pick-more-specific (cdr f) ftype))
                          f))
                    acc)
               (cons field acc)))))
     base
     new-fields))

  ;; Pick the more specific of two types. If one is Any, use the other.
  ;; If neither is a subtype of the other, prefer the first (from earlier allOf member).
  (define (pick-more-specific a b)
    (cond
      ((type-any? a) b)
      ((type-any? b) a)
      ((subtype? a b) a)  ;; a is more specific
      ((subtype? b a) b)  ;; b is more specific
      (else a)))           ;; tie: keep first

  ;; ---------------------------------------------------------------
  ;; Translate enum -> common base type
  ;; ---------------------------------------------------------------
  ;; Per review: map to common base type of enum values, not Symbol.
  ;; String enums -> String, number enums -> Number, mixed -> Any.
  (define (translate-enum values)
    (if (or (not (list? values)) (null? values))
        type:any
        (let ((types (map infer-json-value-type values)))
          (if (for-all (lambda (t) (type=? t (car types))) (cdr types))
              (car types)   ;; all same type -> use that type
              type:any))))  ;; mixed types -> Any

  ;; Infer the type of a JSON literal value (as produced by json-read).
  (define (infer-json-value-type v)
    (cond
      ((string? v) type:string)
      ((number? v) type:number)
      ((boolean? v) type:bool)
      (else type:any)))
)
