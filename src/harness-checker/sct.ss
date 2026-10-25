;; sct.ss
;; Size-change termination core for the harness checker (HC-2).
;;
;; Lee, Jones and Ben-Amram (2001). Each call edge from caller f to callee g
;; carries a size-change graph: an arc (x y strict?) says the value passed
;; for g's parameter y is no larger than f's parameter x, and strictly
;; smaller when strict? is #t. Composing graphs along a path gives the
;; path's graph. A set of edge graphs terminates when every idempotent
;; graph in its composition closure, with G;G = G and src = dst, has a
;; strict arc from some parameter to itself.
;;
;; Parameters are compared with equal?, so a caller may use symbols for
;; formals and pairs for derived measures such as "bound minus formal".
;; Building edge graphs from call expressions is termination.ss's job; this
;; module only composes and judges them.
;;
;; See plans/hc-0cfa.md in the overlord vault for the design.

(library (harness-checker sct)
  (export make-sc-graph
          sc-graph?
          sc-graph-src
          sc-graph-dst
          sc-graph-arcs
          sc-compose
          sc-closure
          sc-check)
  (import (rnrs))

  (define-record-type (sc-graph %make-sc-graph sc-graph?)
    (fields src dst arcs))

  ;; Merge arcs that share (from to), keeping strict when any copy is.
  (define (normalize-arcs arcs)
    (let loop ((arcs arcs) (out '()))
      (if (null? arcs)
          (reverse out)
          (let* ((a (car arcs))
                 (from (car a)) (to (cadr a)) (strict (caddr a))
                 (same? (lambda (b) (and (equal? (car b) from)
                                         (equal? (cadr b) to))))
                 (prev (find same? out)))
            (cond
              ((not prev)
               (loop (cdr arcs) (cons (list from to strict) out)))
              ((and strict (not (caddr prev)))
               (loop (cdr arcs)
                     (cons (list from to #t) (remp same? out))))
              (else (loop (cdr arcs) out)))))))

  (define (arc->string a)
    (call-with-string-output-port (lambda (p) (write a p))))

  ;; Arcs are kept in one canonical order, so equal graphs have equal? arcs.
  (define (make-sc-graph src dst arcs)
    (%make-sc-graph src dst
      (list-sort (lambda (a b) (string<? (arc->string a) (arc->string b)))
                 (normalize-arcs arcs))))

  ;; g1 then g2; requires (sc-graph-dst g1) = (sc-graph-src g2).
  (define (sc-compose g1 g2)
    (make-sc-graph
      (sc-graph-src g1)
      (sc-graph-dst g2)
      (apply append
        (map (lambda (a)
               (map (lambda (b) (list (car a) (cadr b)
                                      (or (caddr a) (caddr b))))
                    (filter (lambda (b) (equal? (cadr a) (car b)))
                            (sc-graph-arcs g2))))
             (sc-graph-arcs g1)))))

  (define (graph-key g)
    (list (sc-graph-src g) (sc-graph-dst g) (sc-graph-arcs g)))

  (define (sc-graph=? g1 g2)
    (equal? (graph-key g1) (graph-key g2)))

  ;; The closure of graphs under composition, or #f when it would hold
  ;; more than cap graphs.
  (define (sc-closure graphs cap)
    (let ((seen (make-hashtable equal-hash equal?)))
      (let loop ((out '()) (count 0) (work graphs))
        (cond
          ((> count cap) #f)
          ((null? work) (reverse out))
          ((hashtable-contains? seen (graph-key (car work)))
           (loop out count (cdr work)))
          (else
           (let* ((g (car work))
                  (out* (cons g out))
                  (after (map (lambda (h) (sc-compose g h))
                              (filter (lambda (h) (equal? (sc-graph-dst g)
                                                          (sc-graph-src h)))
                                      out*)))
                  (before (map (lambda (h) (sc-compose h g))
                               (filter (lambda (h) (equal? (sc-graph-dst h)
                                                           (sc-graph-src g)))
                                       out*))))
             (hashtable-set! seen (graph-key g) #t)
             (loop out* (+ count 1)
                   (append after before (cdr work)))))))))

  (define (idempotent? g)
    (and (equal? (sc-graph-src g) (sc-graph-dst g))
         (sc-graph=? (sc-compose g g) g)))

  (define (strict-self-arc? g)
    (exists (lambda (a) (and (caddr a) (equal? (car a) (cadr a))))
            (sc-graph-arcs g)))

  ;; 'terminates, 'no-descent, or 'limit when the closure exceeds cap.
  (define (sc-check graphs cap)
    (let ((closure (sc-closure graphs cap)))
      (cond
        ((not closure) 'limit)
        ((for-all (lambda (g) (or (not (idempotent? g)) (strict-self-arc? g)))
                  closure)
         'terminates)
        (else 'no-descent))))
)
