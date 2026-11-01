;; One type error and one termination violation.
(define (f x) (string-length x))
(f 42)
(define (spin n) (spin n))
