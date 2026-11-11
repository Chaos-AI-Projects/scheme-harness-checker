;; prelude.ss
;; Loaded ahead of a candidate program and its MultiPL-E tests (HC-51).
;; Stands in for rackunit's check-within and Racket's #hash literals.

;; Racket's check-within: numbers within eps, structures compared recursively.
(define (test-within? actual expected eps)
  (cond ((and (number? actual) (number? expected))
         (and (real? actual) (real? expected)
              (<= (abs (- actual expected)) eps)))
        ((and (pair? actual) (pair? expected))
         (and (test-within? (car actual) (car expected) eps)
              (test-within? (cdr actual) (cdr expected) eps)))
        ((and (vector? actual) (vector? expected))
         (test-within? (vector->list actual) (vector->list expected) eps))
        ((and (hashtable? actual) (hashtable? expected))
         (and (= (hashtable-size actual) (hashtable-size expected))
              (for-all (lambda (k)
                         (and (hashtable-contains? actual k)
                              (test-within? (hashtable-ref actual k #f)
                                            (hashtable-ref expected k #f)
                                            eps)))
                       (vector->list (hashtable-keys expected)))))
        (else (equal? actual expected))))

(define (check-within actual expected eps)
  (unless (test-within? actual expected eps)
    (error 'check-within "expected a different value" actual expected)))

;; #hash((k . v) ...) is rewritten to (make-test-hash '((k . v) ...)).
(define (make-test-hash alist)
  (let ((h (make-hashtable equal-hash equal?)))
    (for-each (lambda (kv) (hashtable-set! h (car kv) (cdr kv))) alist)
    h))
