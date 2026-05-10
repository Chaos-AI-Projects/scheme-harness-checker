;; termination.ss
;; Termination analysis pass for the harness checker.
;; Detects programs that may not terminate (infinite loops / unbounded recursion).
;;
;; Phase 1 (scaffolding): stub returning empty list for all inputs.

(library (harness-checker termination)
  (export check-termination
          make-termination-violation
          termination-violation?
          termination-violation-kind
          termination-violation-function
          termination-violation-expr
          termination-violation-reason)
  (import (rnrs))

  ;; Record type for termination violations.
  ;; Fields:
  ;;   kind     - symbol: 'unbounded-loop | 'unbounded-recursion | 'no-base-case | 'no-exit-condition
  ;;   function - symbol or #f: name of the function/construct involved
  ;;   expr     - the offending s-expression
  ;;   reason   - string: human-readable explanation
  (define-record-type termination-violation
    (fields kind function expr reason))

  ;; check-termination : (list-of expr) x type-env -> (list-of termination-violation)
  ;; Analyzes expressions for potential non-termination.
  ;; Currently a stub that returns an empty list for all inputs.
  (define (check-termination exprs type-env)
    '())
)
