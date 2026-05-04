;; whitelist-checker.ss
;; Function Whitelist Checker for LLM-generated Scheme programs.
;;
;; Approach:
;;   1. Use `read` to parse source into s-expressions
;;   2. Walk the s-expression tree using packrat PEG patterns for
;;      form recognition, with a fused single-pass design that carries
;;      the lexical environment as an inherited attribute (Option B)
;;   3. Collect unbound identifiers (external dependencies)
;;   4. Compare against a deny-by-default whitelist
;;
;; The PEG walker (peg-walker.ss) replaces the hand-coded cond-dispatch
;; walker with packrat pattern matching for form classification.
;; See issue #248 for design rationale.
;;
;; The result is a list of violations: identifiers the program uses
;; that are not locally defined and not in the whitelist.

(library (harness-checker whitelist-checker)
  (export check-file
          check-source
          check-expressions
          read-all-expressions
          collect-unbound
          load-whitelist
          wl-violation-identifier
          wl-violation-context)
  (import (rnrs)
          (harness-checker peg-walker))

  ;; A violation record: an unbound identifier not in the whitelist
  (define-record-type wl-violation
    (fields identifier context))

  ;; Read all s-expressions from a string
  (define (read-all-expressions source)
    (let ((port (open-string-input-port source)))
      (let loop ((exprs '()))
        (let ((expr (read port)))
          (if (eof-object? expr)
              (reverse exprs)
              (loop (cons expr exprs)))))))

  ;; Read all s-expressions from a file
  (define (read-file path)
    (let ((port (open-input-file path)))
      (let loop ((exprs '()))
        (let ((expr (read port)))
          (if (eof-object? expr)
              (begin (close-port port) (reverse exprs))
              (loop (cons expr exprs)))))))

  ;; Load whitelist from a file (one identifier per line)
  (define (load-whitelist path)
    (let ((port (open-input-file path)))
      (let loop ((ids '()))
        (let ((line (get-line port)))
          (if (eof-object? line)
              (begin (close-port port) ids)
              (let ((trimmed (string-trim line)))
                (if (or (string=? trimmed "")
                        (char=? (string-ref trimmed 0) #\;))
                    (loop ids)
                    (loop (cons (string->symbol trimmed) ids)))))))))

  ;; Trim whitespace from a string
  (define (string-trim s)
    (let* ((len (string-length s))
           (start (let loop ((i 0))
                    (if (and (< i len) (char-whitespace? (string-ref s i)))
                        (loop (+ i 1))
                        i)))
           (end (let loop ((i len))
                  (if (and (> i start) (char-whitespace? (string-ref s (- i 1))))
                      (loop (- i 1))
                      i))))
      (substring s start end)))

  ;; Collect all unbound identifiers from a list of expressions.
  ;; Delegates to the PEG-based walker (peg-walker.ss) which uses
  ;; packrat PEG patterns for form recognition with a fused single-pass
  ;; design threading the environment as an inherited attribute.
  ;; Returns a deduplicated list of unbound symbols.
  (define (collect-unbound exprs)
    (peg-collect-unbound exprs))

  ;; Check a list of expressions against a whitelist (list of allowed symbols).
  ;; Returns a list of violation records.
  (define (check-expressions exprs whitelist)
    (let ((unbound (collect-unbound exprs)))
      (filter (lambda (v) v)
              (map (lambda (id)
                     (if (memq id whitelist)
                         #f
                         (make-wl-violation id 'unbound)))
                   unbound))))

  ;; Check source code string against a whitelist.
  (define (check-source source whitelist)
    (let ((exprs (read-all-expressions source)))
      (check-expressions exprs whitelist)))

  ;; Check a file against a whitelist file.
  ;; Returns a list of violation records.
  (define (check-file source-path whitelist-path)
    (let ((exprs (read-file source-path))
          (whitelist (load-whitelist whitelist-path)))
      (check-expressions exprs whitelist)))
)
