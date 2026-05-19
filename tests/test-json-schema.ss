;; test-json-schema.ss
;; Tests for the JSON Schema parser and schema registry.
;;
;; Run with: scheme --libdirs ../src:<packrat-extended-path>:<packrat-examples-path> --program test-json-schema.ss

(import (rnrs)
        (chaos json)
        (harness-checker types)
        (harness-checker json-schema)
        (harness-checker schema-registry))

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

;; Helper: parse a JSON string and convert to type
(define (schema-string->type json-str)
  (json-schema->type (json-read (open-string-input-port json-str))))

;; ===================================================================
;; Test Group: Basic type mappings
;; ===================================================================
(display "Test group: basic type mappings") (newline)

(assert-true "string type"
  (type=? type:string (schema-string->type "{\"type\": \"string\"}")))

(assert-true "number type"
  (type=? type:number (schema-string->type "{\"type\": \"number\"}")))

(assert-true "integer type maps to Number"
  (type=? type:number (schema-string->type "{\"type\": \"integer\"}")))

(assert-true "boolean type"
  (type=? type:bool (schema-string->type "{\"type\": \"boolean\"}")))

(assert-true "null type"
  (type=? type:null (schema-string->type "{\"type\": \"null\"}")))

;; ===================================================================
;; Test Group: Empty and missing schemas
;; ===================================================================
(display "Test group: empty and missing schemas") (newline)

(assert-true "empty object schema"
  (type-any? (schema-string->type "{}")))

(assert-true "schema with no type keyword"
  (type-any? (schema-string->type "{\"description\": \"something\"}")))

;; ===================================================================
;; Test Group: Object -> Record type
;; ===================================================================
(display "Test group: object to record") (newline)

(let ((t (schema-string->type
          "{\"type\": \"object\", \"properties\": {\"name\": {\"type\": \"string\"}, \"age\": {\"type\": \"number\"}}, \"required\": [\"name\"]}")))
  (assert-true "object is record type" (type-record? t))
  (assert-true "object field name is String"
    (type=? type:string (record-field-type t 'name)))
  (assert-true "object field age is Number"
    (type=? type:number (record-field-type t 'age)))
  (assert-equal "object required fields" '(name) (type-record-required t))
  (assert-equal "object has 2 fields" 2 (length (type-record-fields t))))

;; Object without properties -> empty record
(let ((t (schema-string->type "{\"type\": \"object\"}")))
  (assert-true "object no properties is record" (type-record? t))
  (assert-equal "object no properties empty fields" '() (type-record-fields t)))

;; Object with all required
(let ((t (schema-string->type
          "{\"type\": \"object\", \"properties\": {\"x\": {\"type\": \"number\"}, \"y\": {\"type\": \"number\"}}, \"required\": [\"x\", \"y\"]}")))
  (assert-equal "all fields required" 2 (length (type-record-required t))))

;; ===================================================================
;; Test Group: Array -> List type
;; ===================================================================
(display "Test group: array to list") (newline)

(let ((t (schema-string->type "{\"type\": \"array\", \"items\": {\"type\": \"string\"}}")))
  (assert-true "array is list type" (type-list? t))
  (assert-true "array items string"
    (type=? type:string (type-list-elem t))))

(let ((t (schema-string->type "{\"type\": \"array\"}")))
  (assert-true "array no items is list" (type-list? t))
  (assert-true "array no items elem is Any"
    (type-any? (type-list-elem t))))

;; Array of objects
(let ((t (schema-string->type
          "{\"type\": \"array\", \"items\": {\"type\": \"object\", \"properties\": {\"id\": {\"type\": \"number\"}}, \"required\": [\"id\"]}}")))
  (assert-true "array of objects is list" (type-list? t))
  (assert-true "array of objects elem is record"
    (type-record? (type-list-elem t)))
  (assert-true "array of objects elem has id"
    (type=? type:number (record-field-type (type-list-elem t) 'id))))

;; ===================================================================
;; Test Group: Nested objects
;; ===================================================================
(display "Test group: nested objects") (newline)

(let ((t (schema-string->type
          "{\"type\": \"object\", \"properties\": {\"address\": {\"type\": \"object\", \"properties\": {\"city\": {\"type\": \"string\"}, \"zip\": {\"type\": \"string\"}}, \"required\": [\"city\"]}}, \"required\": [\"address\"]}")))
  (assert-true "nested record" (type-record? t))
  (let ((addr-type (record-field-type t 'address)))
    (assert-true "nested field is record" (type-record? addr-type))
    (assert-true "nested field city is String"
      (type=? type:string (record-field-type addr-type 'city)))
    (assert-true "nested field zip is String"
      (type=? type:string (record-field-type addr-type 'zip)))
    (assert-equal "nested required" '(city) (type-record-required addr-type))))

;; ===================================================================
;; Test Group: enum -> common base type
;; ===================================================================
(display "Test group: enum") (newline)

(assert-true "string enum -> String"
  (type=? type:string (schema-string->type "{\"enum\": [\"red\", \"green\", \"blue\"]}")))

(assert-true "number enum -> Number"
  (type=? type:number (schema-string->type "{\"enum\": [1, 2, 3]}")))

(assert-true "bool enum -> Bool"
  (type=? type:bool (schema-string->type "{\"enum\": [true, false]}")))

(assert-true "mixed enum -> Any"
  (type-any? (schema-string->type "{\"enum\": [\"hello\", 42, true]}")))

(assert-true "empty enum -> Any"
  (type-any? (schema-string->type "{\"enum\": []}")))

;; ===================================================================
;; Test Group: anyOf / oneOf -> Union
;; ===================================================================
(display "Test group: anyOf / oneOf") (newline)

(let ((t (schema-string->type
          "{\"anyOf\": [{\"type\": \"string\"}, {\"type\": \"number\"}]}")))
  (assert-true "anyOf is union" (type-union? t))
  (assert-equal "anyOf has 2 members" 2 (length (type-union-members t))))

(let ((t (schema-string->type
          "{\"oneOf\": [{\"type\": \"string\"}, {\"type\": \"number\"}]}")))
  (assert-true "oneOf is union" (type-union? t))
  (assert-equal "oneOf has 2 members" 2 (length (type-union-members t))))

;; Single-member anyOf collapses
(let ((t (schema-string->type
          "{\"anyOf\": [{\"type\": \"string\"}]}")))
  (assert-true "single anyOf collapses"
    (type=? type:string t)))

;; anyOf with duplicate types collapses
(let ((t (schema-string->type
          "{\"anyOf\": [{\"type\": \"string\"}, {\"type\": \"string\"}]}")))
  (assert-true "duplicate anyOf collapses"
    (type=? type:string t)))

;; ===================================================================
;; Test Group: allOf -> merge records
;; ===================================================================
(display "Test group: allOf") (newline)

;; Two objects merged
(let ((t (schema-string->type
          "{\"allOf\": [{\"type\": \"object\", \"properties\": {\"name\": {\"type\": \"string\"}}, \"required\": [\"name\"]}, {\"type\": \"object\", \"properties\": {\"age\": {\"type\": \"number\"}}, \"required\": [\"age\"]}]}")))
  (assert-true "allOf merge is record" (type-record? t))
  (assert-true "allOf merge has name"
    (type=? type:string (record-field-type t 'name)))
  (assert-true "allOf merge has age"
    (type=? type:number (record-field-type t 'age)))
  ;; Both name and age should be required
  (assert-true "allOf merge name required" (and (memq 'name (type-record-required t)) #t))
  (assert-true "allOf merge age required" (and (memq 'age (type-record-required t)) #t)))

;; allOf with non-object falls back to Any
(let ((t (schema-string->type
          "{\"allOf\": [{\"type\": \"string\"}, {\"type\": \"number\"}]}")))
  (assert-true "allOf non-objects -> Any" (type-any? t)))

;; allOf with overlapping field (stricter type wins)
(let ((t (schema-string->type
          "{\"allOf\": [{\"type\": \"object\", \"properties\": {\"data\": {\"type\": \"array\", \"items\": {\"type\": \"number\"}}}}, {\"type\": \"object\", \"properties\": {\"data\": {\"type\": \"array\"}}}]}")))
  (assert-true "allOf overlapping field is record" (type-record? t))
  ;; The more specific type (array of number) should win over (array of any)
  (let ((data-type (record-field-type t 'data)))
    (assert-true "allOf overlapping field is list" (type-list? data-type))
    (assert-true "allOf overlapping field specific type wins"
      (type=? type:number (type-list-elem data-type)))))

;; ===================================================================
;; Test Group: type as array (nullable fields)
;; ===================================================================
(display "Test group: type as array") (newline)

;; JSON Schema allows "type": ["string", "null"] for nullable fields.
;; Our translator falls back to Any for array type values.
(assert-true "type as array falls back to Any"
  (type-any? (schema-string->type "{\"type\": [\"string\", \"null\"]}")))

(assert-true "type as single-element array falls back to Any"
  (type-any? (schema-string->type "{\"type\": [\"number\"]}")))

;; ===================================================================
;; Test Group: Registry error handling
;; ===================================================================
(display "Test group: registry error handling") (newline)

;; Non-object top-level value (array) -> empty alist
(let ((test-file "test-registry-array.json"))
  (call-with-port (open-file-output-port test-file
                    (file-options no-fail)
                    (buffer-mode block)
                    (native-transcoder))
    (lambda (port)
      (put-string port "[1, 2, 3]")))
  (let ((schemas (load-tool-schemas test-file)))
    (assert-equal "non-object registry returns empty" '() schemas))
  (delete-file test-file))

;; Non-object top-level value (string) -> empty alist
(let ((test-file "test-registry-string.json"))
  (call-with-port (open-file-output-port test-file
                    (file-options no-fail)
                    (buffer-mode block)
                    (native-transcoder))
    (lambda (port)
      (put-string port "\"just a string\"")))
  (let ((schemas (load-tool-schemas test-file)))
    (assert-equal "string registry returns empty" '() schemas))
  (delete-file test-file))

;; Empty object -> empty alist
(let ((test-file "test-registry-empty.json"))
  (call-with-port (open-file-output-port test-file
                    (file-options no-fail)
                    (buffer-mode block)
                    (native-transcoder))
    (lambda (port)
      (put-string port "{}")))
  (let ((schemas (load-tool-schemas test-file)))
    (assert-equal "empty object registry returns empty" '() schemas))
  (delete-file test-file))

;; ===================================================================
;; Test Group: Round-trip (json-schema->type -> type->string)
;; ===================================================================
(display "Test group: round-trip type->string") (newline)

(assert-equal "string round-trip" "String"
  (type->string (schema-string->type "{\"type\": \"string\"}")))

(assert-equal "number round-trip" "Number"
  (type->string (schema-string->type "{\"type\": \"number\"}")))

(assert-equal "bool round-trip" "Bool"
  (type->string (schema-string->type "{\"type\": \"boolean\"}")))

(assert-equal "array of string round-trip" "(List String)"
  (type->string (schema-string->type "{\"type\": \"array\", \"items\": {\"type\": \"string\"}}")))

;; Object round-trip (field order may vary so check parts)
(let ((s (type->string (schema-string->type
          "{\"type\": \"object\", \"properties\": {\"x\": {\"type\": \"number\"}}, \"required\": [\"x\"]}"))))
  (assert-true "object round-trip contains Record"
    (string=? s "(Record (x: Number))")))

;; ===================================================================
;; Test Group: Schema registry
;; ===================================================================
(display "Test group: schema registry") (newline)

;; Create a temporary JSON file for testing
(let ((test-file "test-tool-schemas.json"))
  (call-with-port (open-file-output-port test-file
                    (file-options no-fail)
                    (buffer-mode block)
                    (native-transcoder))
    (lambda (port)
      (put-string port "{\"get-weather\": {\"type\": \"object\", \"properties\": {\"location\": {\"type\": \"string\"}, \"unit\": {\"type\": \"string\"}}, \"required\": [\"location\"]}, \"calculate\": {\"type\": \"object\", \"properties\": {\"expression\": {\"type\": \"string\"}}, \"required\": [\"expression\"]}}")))

  (let ((schemas (load-tool-schemas test-file)))
    (assert-equal "registry loads 2 tools" 2 (length schemas))

    ;; Check get-weather
    (let ((gw (assq 'get-weather schemas)))
      (assert-true "registry has get-weather" (pair? gw))
      (assert-true "get-weather is record" (type-record? (cdr gw)))
      (assert-true "get-weather has location"
        (type=? type:string (record-field-type (cdr gw) 'location)))
      (assert-true "get-weather has unit"
        (type=? type:string (record-field-type (cdr gw) 'unit)))
      (assert-true "get-weather location required"
        (and (memq 'location (type-record-required (cdr gw))) #t)))

    ;; Check calculate
    (let ((calc (assq 'calculate schemas)))
      (assert-true "registry has calculate" (pair? calc))
      (assert-true "calculate is record" (type-record? (cdr calc)))
      (assert-true "calculate has expression"
        (type=? type:string (record-field-type (cdr calc) 'expression)))))

  ;; Clean up
  (delete-file test-file))

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
