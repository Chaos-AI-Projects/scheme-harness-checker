;; sample-safe.ss
;; A sample program that should pass the whitelist checker.

(define (fibonacci n)
  (let loop ((i 0) (a 0) (b 1))
    (if (= i n)
        a
        (loop (+ i 1) b (+ a b)))))

(define (factorial n)
  (letrec ((fact (lambda (n acc)
                   (if (<= n 0)
                       acc
                       (fact (- n 1) (* acc n))))))
    (fact n 1)))

(display (fibonacci 10))
(newline)
(display (factorial 10))
(newline)
