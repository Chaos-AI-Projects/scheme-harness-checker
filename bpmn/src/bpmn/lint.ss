;; lint.ss
;; Structural lint of a BPMN model: checks on the shape of the sequence-flow
;; graph alone. Every check but dangling-flow matches a bpmnlint rule (HC-62).
;;
;; Violations come grouped by check, in the order below, and in document order
;; within a check. The reader's own unsupported-element violations are not
;; repeated here.

(library (bpmn lint)
  (export bpmn-lint)
  (import (rnrs) (bpmn model))

  (define (bpmn-lint m)
    (let ((nodes (bpmn-model-nodes m))
          (flows (bpmn-model-flows m))
          (process (bpmn-model-process-id m)))

      (define (incoming n)
        (filter (lambda (f) (equal? (bpmn-flow-target f) (bpmn-node-id n))) flows))
      (define (outgoing n)
        (filter (lambda (f) (equal? (bpmn-flow-source f) (bpmn-node-id n))) flows))
      (define (of-kind? n kinds) (and (memq (bpmn-node-kind n) kinds) #t))
      (define (gateway? n) (of-kind? n '(exclusive parallel inclusive)))
      ;; An empty or blank conditionExpression is no condition.
      (define (conditional? f)
        (let ((c (bpmn-flow-condition f)))
          (and c (> (string-length c) 0))))
      (define (violation kind id detail) (make-bpmn-violation kind id detail))

      ;; start-event-required and end-event-required
      (define (missing-event kind label)
        (if (exists (lambda (n) (eq? (bpmn-node-kind n) kind)) nodes)
            '()
            (list (violation (if (eq? kind 'start) 'no-start-event 'no-end-event) process
                             (string-append "the process has no " label " event")))))

      ;; Not a bpmnlint rule, whose model resolves every reference: a flow
      ;; whose source or target names no flow node would otherwise go unseen.
      (define (dangling f)
        (define (end-of label ref)
          (if (exists (lambda (n) (string=? (bpmn-node-id n) ref)) nodes)
              '()
              (list (violation 'dangling-flow (bpmn-flow-id f)
                               (string-append "its " label " " ref " is not a flow node")))))
        (append (end-of "source" (bpmn-flow-source f)) (end-of "target" (bpmn-flow-target f))))

      ;; no-disconnected, no-implicit-start and no-implicit-end together: a start
      ;; event needs an outgoing flow, an end event an incoming one, and every
      ;; other node both.
      (define (disconnected n)
        (let ((no-in (and (not (of-kind? n '(start))) (null? (incoming n))))
              (no-out (and (not (of-kind? n '(end))) (null? (outgoing n)))))
          (cond
            ((and no-in no-out) (list (violation 'disconnected (bpmn-node-id n) "no incoming and no outgoing flow")))
            (no-in (list (violation 'disconnected (bpmn-node-id n) "no incoming flow")))
            (no-out (list (violation 'disconnected (bpmn-node-id n) "no outgoing flow")))
            (else '()))))

      ;; no-implicit-split: a node other than a gateway with more than one
      ;; outgoing flow that has no condition and is not the default.
      (define (implicit-split n)
        (if (and (not (gateway? n))
                 (> (length (filter (lambda (f) (not (or (conditional? f) (bpmn-flow-default? f))))
                                    (outgoing n)))
                    1))
            (list (violation 'implicit-split (bpmn-node-id n) "more than one outgoing flow without a condition"))
            '()))

      ;; conditional-flows: every flow out of a split has a condition, except
      ;; its default. A node is a split here when it has more than one outgoing
      ;; flow and is an exclusive or inclusive gateway, or has a conditional or
      ;; default flow out of it.
      (define (missing-condition n)
        (let ((out (outgoing n)))
          (if (and (> (length out) 1)
                   (or (of-kind? n '(exclusive inclusive))
                       (exists (lambda (f) (or (conditional? f) (bpmn-flow-default? f))) out)))
              (map (lambda (f)
                     (violation 'missing-condition (bpmn-flow-id f)
                                (string-append "a flow out of the split " (bpmn-node-id n)
                                               " has no condition and is not its default")))
                   (filter (lambda (f) (not (or (conditional? f) (bpmn-flow-default? f)))) out))
              '())))

      ;; no-gateway-join-fork
      (define (gateway-join-fork n)
        (if (and (gateway? n) (> (length (incoming n)) 1) (> (length (outgoing n)) 1))
            (list (violation 'gateway-join-fork (bpmn-node-id n) "the gateway both joins and forks"))
            '()))

      ;; no-duplicate-sequence-flows: each later flow with the same source,
      ;; target and condition as an earlier one is reported against the first.
      (define (same-flow? a b)
        (and (equal? (bpmn-flow-source a) (bpmn-flow-source b))
             (equal? (bpmn-flow-target a) (bpmn-flow-target b))
             (equal? (bpmn-flow-condition a) (bpmn-flow-condition b))))
      (define duplicates
        (let loop ((fs flows) (earlier '()) (acc '()))
          (if (null? fs)
              (reverse acc)
              (let* ((f (car fs))
                     (first (find (lambda (e) (same-flow? e f)) (reverse earlier))))
                (loop (cdr fs) (cons f earlier)
                      (if first
                          (cons (violation 'duplicate-flow (bpmn-flow-id f)
                                           (string-append "same source, target and condition as "
                                                          (bpmn-flow-id first)))
                                acc)
                          acc))))))

      (define (per-node check) (apply append (map check nodes)))

      (append (missing-event 'start "start")
              (missing-event 'end "end")
              (apply append (map dangling flows))
              (per-node disconnected)
              (per-node implicit-split)
              (per-node missing-condition)
              (per-node gateway-join-fork)
              duplicates))))
