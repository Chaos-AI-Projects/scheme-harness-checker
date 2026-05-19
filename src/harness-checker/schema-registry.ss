;; schema-registry.ss
;; Tool schema registry: loads JSON Schema definitions for tools and converts
;; them into the internal type representation for use during type inference.
;;
;; Input format: a JSON file containing an object mapping tool names to their
;; JSON Schema definitions, e.g.:
;;   {
;;     "get-weather": {
;;       "type": "object",
;;       "properties": { "location": { "type": "string" } },
;;       "required": ["location"]
;;     }
;;   }
;;
;; Output: an alist of (symbol . type) compatible with load-type-signatures,
;; suitable for merging with the existing signatures alist.

(library (harness-checker schema-registry)
  (export load-tool-schemas)
  (import (rnrs)
          (chaos json)
          (harness-checker types)
          (harness-checker json-schema))  ;; json-schema->type, json-object?

  ;; Load tool schemas from a JSON file.
  ;; Returns an alist of (symbol . type) where each tool name maps to
  ;; a Record type derived from its JSON Schema.
  ;; The output is compatible with the signatures alist used by check-types.
  (define (load-tool-schemas path)
    (let ((obj (call-with-port (open-input-file path)
                 (lambda (port) (json-read port)))))
      (if (not (json-object? obj))
          ;; Not a JSON object -> return empty alist
          '()
          ;; Convert each tool entry
          (let loop ((i 0) (acc '()))
            (if (>= i (vector-length obj))
                (reverse acc)
                (let* ((entry (vector-ref obj i))
                       (name (string->symbol (car entry)))
                       (schema (cdr entry))
                       (tool-type (json-schema->type schema)))
                  (loop (+ i 1)
                        (cons (cons name tool-type) acc))))))))
)
