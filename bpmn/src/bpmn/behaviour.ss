;; behaviour.ss
;; The behaviour check of a BPMN model: explore every reachable state and report
;; what cannot run or cannot finish (HC-63).
;;
;; A state is the multiset of sequence flows holding a token, kept as a sorted
;; list of flow indices. Each start event begins a run. Conditions are coin
;; flips, so a split may send its token down any flow it could take. A state
;; with no tokens is final. A state with two tokens on one flow is reported as
;; unsafe-flow and not explored past, so every explored state has at most one
;; token per flow and the state space is finite.
;;
;; Violations come grouped by kind in this order: state-limit, unsafe-flow,
;; deadlock, cannot-complete, dead-task, dead-flow. When the state limit is hit
;; only state-limit, unsafe-flow and deadlock are reported, since the others
;; need every state.

(library (bpmn behaviour)
  (export bpmn-behaviour bpmn-default-state-limit)
  (import (rnrs) (bpmn model))

  (define bpmn-default-state-limit 100000)

  (define (iota n)
    (let loop ((k (- n 1)) (acc '()))
      (if (< k 0) acc (loop (- k 1) (cons k acc)))))

  (define bpmn-behaviour
    (case-lambda
      ((m) (bpmn-behaviour m bpmn-default-state-limit))
      ((m limit) (explore m limit))))

  (define (explore m limit)
    (let* ((nodes (bpmn-model-nodes m))
           (flows (list->vector (bpmn-model-flows m)))
           (nflows (vector-length flows))
           (process (bpmn-model-process-id m)))

      (define (flow-index pred)
        (let loop ((k 0) (acc '()))
          (if (= k nflows)
              (reverse acc)
              (loop (+ k 1) (if (pred (vector-ref flows k)) (cons k acc) acc)))))
      (define (incoming n)
        (flow-index (lambda (f) (equal? (bpmn-flow-target f) (bpmn-node-id n)))))
      (define (outgoing n)
        (flow-index (lambda (f) (equal? (bpmn-flow-source f) (bpmn-node-id n)))))
      (define (flow-id k) (bpmn-flow-id (vector-ref flows k)))
      (define (conditional? k)
        (let ((c (bpmn-flow-condition (vector-ref flows k))))
          (and c (> (string-length c) 0))))
      (define (default? k) (bpmn-flow-default? (vector-ref flows k)))

      ;; node id -> (node incoming outgoing)
      (define table
        (map (lambda (n) (list n (incoming n) (outgoing n))) nodes))
      (define by-id
        (let ((h (make-hashtable string-hash string=?)))
          (for-each (lambda (e) (unless (hashtable-contains? h (bpmn-node-id (car e)))
                                  (hashtable-set! h (bpmn-node-id (car e)) e)))
                    table)
          h))
      (define (assoc-node id) (hashtable-ref by-id id #f))

      ;; The sets of flows a node may put tokens on when it fires.
      ;; Every flow out of a parallel gateway gets one; an exclusive gateway
      ;; picks one. Any other node acts as BPMN's inclusive split: each flow
      ;; without a condition always gets a token, any choice of the
      ;; conditional ones may, and the default gets one only when no
      ;; conditional flow is chosen. Choosing nothing at all is not a way to
      ;; fire, since BPMN raises an error there.
      (define (emissions kind out)
        (cond
          ((null? out) '(()))
          ((eq? kind 'parallel) (list out))
          ((eq? kind 'exclusive) (map list out))
          (else
           (let ((dflt (filter default? out))
                 (cond-flows (filter (lambda (k) (and (conditional? k) (not (default? k)))) out))
                 (always (filter (lambda (k) (not (or (conditional? k) (default? k)))) out)))
             (filter pair?
                     (map (lambda (s) (append always (if (null? s) dflt s)))
                          (subsets cond-flows)))))))

      (define (subsets xs)
        (if (null? xs)
            '(())
            (let ((rest (subsets (cdr xs))))
              (append rest (map (lambda (s) (cons (car xs) s)) rest)))))

      ;; Node ids from which the source of any flow in KS can be reached without
      ;; passing through node STOP, those sources included.
      (define (upstream-nodes ks stop)
        (let loop ((todo (map (lambda (k) (bpmn-flow-source (vector-ref flows k))) ks)) (seen '()))
          (cond
            ((null? todo) seen)
            ((or (member (car todo) seen) (string=? (car todo) stop)) (loop (cdr todo) seen))
            (else
             (let ((e (assoc-node (car todo))))
               (loop (append (if e
                                 (map (lambda (k) (bpmn-flow-source (vector-ref flows k))) (cadr e))
                                 '())
                             (cdr todo))
                     (cons (car todo) seen)))))))

      ;; BPMN 2.0's inclusive join rule: the gateway G may fire when some
      ;; incoming flow holds a token and no token elsewhere can still reach an
      ;; empty incoming flow. A path does not count when it passes through G or
      ;; through a node that can reach one of G's non-empty incoming flows.
      (define (inclusive-ready? g in state)
        (let* ((full (filter (lambda (k) (memv k state)) in))
               (empty (filter (lambda (k) (not (memv k state))) in)))
          (and (pair? full)
               (let ((blocked (cons (bpmn-node-id g) (upstream-nodes full (bpmn-node-id g))))
                     (targets (map (lambda (k) (bpmn-flow-source (vector-ref flows k))) empty)))
                 (not (exists
                       (lambda (t)
                         (and (not (memv t in))
                              (reaches? (bpmn-flow-target (vector-ref flows t)) targets blocked)))
                       state))))))

      ;; Can node FROM reach any node in TARGETS without entering BLOCKED?
      (define (reaches? from targets blocked)
        (let loop ((todo (list from)) (seen '()))
          (cond
            ((null? todo) #f)
            ((or (member (car todo) seen) (member (car todo) blocked)) (loop (cdr todo) seen))
            ((member (car todo) targets) #t)
            (else
             (let ((e (assoc-node (car todo))))
               (loop (append (if e
                                 (map (lambda (k) (bpmn-flow-target (vector-ref flows k))) (caddr e))
                                 '())
                             (cdr todo))
                     (cons (car todo) seen)))))))

      (define (remove-one k state)
        (cond ((null? state) '())
              ((= k (car state)) (cdr state))
              (else (cons (car state) (remove-one k (cdr state))))))
      (define (add-all ks state) (list-sort < (append ks state)))

      ;; Each way a node can fire in STATE: (node-id . next-state).
      (define (successors state)
        (apply append
               (map (lambda (e)
                      (let* ((n (car e)) (in (cadr e)) (out (caddr e)) (kind (bpmn-node-kind n))
                             (fire (lambda (taken)
                                     (map (lambda (emit)
                                            (cons (bpmn-node-id n)
                                                  (add-all emit (fold-left (lambda (s k) (remove-one k s)) state taken))))
                                          (emissions kind out)))))
                        (case kind
                          ((start) '())
                          ((parallel)
                           (if (and (pair? in) (for-all (lambda (k) (memv k state)) in)) (fire in) '()))
                          ((inclusive)
                           (if (inclusive-ready? n in state)
                               (fire (filter (lambda (k) (memv k state)) in))
                               '()))
                          (else
                           (apply append (map (lambda (k) (if (memv k state) (fire (list k)) '())) in))))))
                    table)))

      (define (unsafe? state)
        (and (pair? state)
             (let loop ((s state))
               (cond ((null? (cdr s)) #f)
                     ((= (car s) (cadr s)) #t)
                     (else (loop (cdr s)))))))

      (define (tokens-text state)
        (let loop ((ks (unique state)) (acc ""))
          (cond ((null? ks) acc)
                ((string=? acc "") (loop (cdr ks) (flow-id (car ks))))
                (else (loop (cdr ks) (string-append acc ", " (flow-id (car ks))))))))
      (define (unique s)
        (cond ((null? s) '())
              ((and (pair? (cdr s)) (= (car s) (cadr s))) (unique (cdr s)))
              (else (cons (car s) (unique (cdr s))))))
      (define (violation kind id detail) (make-bpmn-violation kind id detail))

      (let ((starts (filter (lambda (n) (eq? (bpmn-node-kind n) 'start)) nodes)))
        (if (null? starts)
            '()
            (let ((index (make-hashtable equal-hash equal?))
                  (by-index (make-eqv-hashtable))
                  (edges '())           ; (from-index . to-index), reversed
                  (fired (make-hashtable string-hash string=?))
                  (live-flows (make-vector nflows #f))
                  (unsafe-flows '())
                  (stuck '())           ; expanded non-final states with no successor
                  (over-limit #f)
                  (count 0))

              ;; Record STATE as reached and return its index, or #f past the limit.
              (define (visit! state)
                (or (hashtable-ref index state #f)
                    (if (>= count limit)
                        (begin (set! over-limit #t) #f)
                        (let ((i count))
                          (hashtable-set! index state i)
                          (hashtable-set! by-index i state)
                          (set! count (+ count 1))
                          (for-each (lambda (k) (vector-set! live-flows k #t)) state)
                          (when (unsafe? state)
                            (for-each (lambda (k) (unless (memv k unsafe-flows)
                                                    (set! unsafe-flows (cons k unsafe-flows))))
                                      (let loop ((s state) (acc '()))
                                        (cond ((or (null? s) (null? (cdr s))) acc)
                                              ((= (car s) (cadr s)) (loop (cdr s) (cons (car s) acc)))
                                              (else (loop (cdr s) acc))))))
                          i))))

              (define initial
                (apply append
                       (map (lambda (s)
                              (hashtable-set! fired (bpmn-node-id s) #t)
                              (map (lambda (emit) (add-all emit '()))
                                   (emissions 'start (caddr (assoc-node (bpmn-node-id s))))))
                            starts)))

              (define initial-indices
                (let ((is (map visit! initial)))
                  (filter (lambda (x) x) is)))

              ;; States are numbered as they are found, so expanding them in
              ;; index order is a breadth-first search.
              (let loop ((i 0))
                (unless (or (= i count) over-limit)
                  (let ((state (hashtable-ref by-index i #f)))
                    (unless (unsafe? state)
                      (let ((moves (successors state)))
                        (when (and (pair? state) (null? moves))
                          (set! stuck (cons i stuck)))
                        (for-each
                         (lambda (s)
                           (hashtable-set! fired (car s) #t)
                           (let ((j (visit! (cdr s))))
                             (when j (set! edges (cons (cons i j) edges)))))
                         moves)))
                    (loop (+ i 1)))))

              (let* ((n count)
                     (all (let ((v (make-vector n)))
                            (for-each (lambda (i) (vector-set! v i (hashtable-ref by-index i #f))) (iota n))
                            v))
                     (pred (make-vector n '())))
                (for-each (lambda (e)
                            (vector-set! pred (cdr e) (cons (car e) (vector-ref pred (cdr e)))))
                          edges)
                (let* ((deadlocks (list-sort < stuck))
                       (deadlock? (let ((v (make-vector n #f)))
                                    (for-each (lambda (i) (vector-set! v i #t)) stuck)
                                    v))
                       (head
                        (append
                         (if over-limit
                             (list (violation 'state-limit process
                                              (string-append "more than " (number->string limit) " states")))
                             '())
                         (map (lambda (k) (violation 'unsafe-flow (flow-id k) "a second token reaches the flow"))
                              (list-sort < unsafe-flows))
                         (map (lambda (i)
                                (let ((s (vector-ref all i)))
                                  (violation 'deadlock (flow-id (car s))
                                             (string-append "no node can fire, with tokens on " (tokens-text s)))))
                              deadlocks))))
                  (if over-limit
                      head
                      ;; A state is settled when it can reach a final state, a
                      ;; deadlock or an unsafe state; the last two are reported
                      ;; already. An unsettled state is reported only where a run
                      ;; enters the unsettled part: an initial state, or one with
                      ;; a settled predecessor.
                      (let ((settled (make-vector n #f)))
                        (let mark ((todo (filter (lambda (i)
                                                   (let ((s (vector-ref all i)))
                                                     (or (null? s) (unsafe? s) (vector-ref deadlock? i))))
                                                 (iota n))))
                          (unless (null? todo)
                            (let ((i (car todo)))
                              (if (vector-ref settled i)
                                  (mark (cdr todo))
                                  (begin
                                    (vector-set! settled i #t)
                                    (mark (append (vector-ref pred i) (cdr todo))))))))
                        (append
                         head
                         (map (lambda (i)
                                (let ((s (vector-ref all i)))
                                  (violation 'cannot-complete (flow-id (car s))
                                             (string-append "no run can finish from tokens on " (tokens-text s)))))
                              (filter (lambda (i)
                                        (and (not (vector-ref settled i))
                                             (or (memv i initial-indices)
                                                 (exists (lambda (p) (vector-ref settled p)) (vector-ref pred i)))))
                                      (iota n)))
                         (map (lambda (t) (violation 'dead-task (bpmn-node-id t) "the task never runs"))
                              (filter (lambda (t) (and (eq? (bpmn-node-kind t) 'task)
                                                       (not (hashtable-ref fired (bpmn-node-id t) #f))))
                                      nodes))
                         (map (lambda (k) (violation 'dead-flow (flow-id k) "the flow never holds a token"))
                              (filter (lambda (k) (not (vector-ref live-flows k))) (iota nflows))))))))))))))
