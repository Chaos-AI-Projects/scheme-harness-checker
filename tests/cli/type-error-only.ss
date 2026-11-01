;; One type error, nothing else: f wants a string and gets a number.
(define (f x) (string-length x))
(f 42)
