;; test-lint.ss
;; Tests for the BPMN structural lint (HC-62).
;;
;; Run with: scheme --libdirs ../src --program test-lint.ss

(import (rnrs) (bpmn model) (bpmn lint))

(define pass-count 0)
(define fail-count 0)

(define (assert-equal test-name expected actual)
  (if (equal? expected actual)
      (begin
        (set! pass-count (+ pass-count 1))
        (display "  PASS: ") (display test-name) (newline))
      (begin
        (set! fail-count (+ fail-count 1))
        (display "  FAIL: ") (display test-name) (newline)
        (display "    expected: ") (write expected) (newline)
        (display "    actual:   ") (write actual) (newline))))

(define (chart process-body)
  (string-append
   "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
   "<bpmn:definitions xmlns:bpmn=\"http://www.omg.org/spec/BPMN/20100524/MODEL\" id=\"defs\">"
   "<bpmn:process id=\"P\" isExecutable=\"true\">" process-body "</bpmn:process>"
   "</bpmn:definitions>"))

;; The lint violations of a chart, as (kind id detail) lists.
(define (lint . body)
  (map (lambda (v) (list (bpmn-violation-kind v) (bpmn-violation-id v) (bpmn-violation-detail v)))
       (bpmn-lint (bpmn-read-string (chart (apply string-append body))))))

(define (seq from to id)
  (string-append "<bpmn:sequenceFlow id=\"" id "\" sourceRef=\"" from "\" targetRef=\"" to "\"/>"))
(define (cseq from to id condition)
  (string-append "<bpmn:sequenceFlow id=\"" id "\" sourceRef=\"" from "\" targetRef=\"" to "\">"
                 "<bpmn:conditionExpression>" condition "</bpmn:conditionExpression>"
                 "</bpmn:sequenceFlow>"))
(define (node kind id . attrs)
  (string-append "<bpmn:" kind " id=\"" id "\"" (apply string-append attrs) "/>"))
(define start (node "startEvent" "S"))
(define end (node "endEvent" "E"))

;; ===================================================================
(display "Test group: a well-formed chart") (newline)

(assert-equal "a chart with no structural fault has no violations"
              '()
              (lint start (node "task" "T") (node "exclusiveGateway" "G" " default=\"f4\"")
                    (node "task" "A") (node "exclusiveGateway" "M") end
                    (seq "S" "T" "f1") (seq "T" "G" "f2") (cseq "G" "A" "f3" "x &gt; 1") (seq "G" "M" "f4")
                    (seq "A" "M" "f5") (seq "M" "E" "f6")))

(assert-equal "the lint ignores the reader's unsupported-element violations"
              '()
              (lint start (node "callActivity" "C") end (seq "S" "C" "f1") (seq "C" "E" "f2")))

;; ===================================================================
(display "Test group: start and end events") (newline)

(assert-equal "a process without a start event"
              '((no-start-event "P" "the process has no start event")
                (disconnected "T" "no incoming flow"))
              (lint (node "task" "T") end (seq "T" "E" "f1")))

(assert-equal "a process without an end event"
              '((no-end-event "P" "the process has no end event")
                (disconnected "T" "no outgoing flow"))
              (lint start (node "task" "T") (seq "S" "T" "f1")))

(assert-equal "two start events and two end events are allowed"
              '()
              (lint start (node "startEvent" "S2") (node "task" "T") end (node "endEvent" "E2")
                    (seq "S" "T" "f1") (seq "S2" "T" "f2") (cseq "T" "E" "f3" "a") (cseq "T" "E2" "f4" "b")))

(assert-equal "an empty process"
              '((no-start-event "P" "the process has no start event")
                (no-end-event "P" "the process has no end event"))
              (lint))

;; ===================================================================
(display "Test group: dangling-flow") (newline)

(assert-equal "a flow whose target is not a flow node"
              '((dangling-flow "f3" "its target GHOST is not a flow node"))
              (lint start (node "exclusiveGateway" "G") end
                    (seq "S" "G" "f1") (cseq "G" "E" "f2" "x") (cseq "G" "GHOST" "f3" "y")))

(assert-equal "a flow whose source is a data object"
              '((dangling-flow "f2" "its source D is not a flow node"))
              (lint start "<bpmn:dataObject id=\"D\"/>" end (seq "S" "E" "f1") (seq "D" "E" "f2")))

(assert-equal "a flow with neither end a flow node"
              '((dangling-flow "f2" "its source X is not a flow node")
                (dangling-flow "f2" "its target Y is not a flow node"))
              (lint start end (seq "S" "E" "f1") (seq "X" "Y" "f2")))

(display "Test group: disconnected") (newline)

(assert-equal "a task with no flows at all"
              '((disconnected "X" "no incoming and no outgoing flow"))
              (lint start (node "task" "X") end (seq "S" "E" "f1")))

(assert-equal "a gateway with no outgoing flow"
              '((disconnected "G" "no outgoing flow"))
              (lint start (node "startEvent" "S2") (node "parallelGateway" "G") end
                    (seq "S" "G" "f1") (seq "S2" "E" "f2")))

(assert-equal "a start event with no outgoing flow"
              '((disconnected "S2" "no outgoing flow"))
              (lint start (node "startEvent" "S2") end (seq "S" "E" "f1")))

(assert-equal "an end event with no incoming flow"
              '((disconnected "E2" "no incoming flow"))
              (lint start end (node "endEvent" "E2") (seq "S" "E" "f1")))

(assert-equal "a flattened sub-process's inner events count as connected"
              '()
              (lint start
                    "<bpmn:subProcess id=\"SP\">"
                    (node "startEvent" "SS") (node "task" "I") (node "endEvent" "SE")
                    (seq "SS" "I" "g1") (seq "I" "SE" "g2")
                    "</bpmn:subProcess>"
                    end (seq "S" "SP" "f1") (seq "SP" "E" "f2")))

;; ===================================================================
(display "Test group: implicit-split") (newline)

(assert-equal "a task with two unconditional outgoing flows"
              '((implicit-split "T" "more than one outgoing flow without a condition"))
              (lint start (node "task" "T") end (node "endEvent" "E2")
                    (seq "S" "T" "f1") (seq "T" "E" "f2") (seq "T" "E2" "f3")))

(assert-equal "a start event with two unconditional outgoing flows"
              '((implicit-split "S" "more than one outgoing flow without a condition"))
              (lint start (node "task" "A") end
                    (seq "S" "A" "f1") (seq "S" "E" "f2") (seq "A" "E" "f3")))

(assert-equal "a task with one unconditional and one conditional outgoing flow"
              '((missing-condition "f2" "a flow out of the split T has no condition and is not its default"))
              (lint start (node "task" "T") end (node "endEvent" "E2")
                    (seq "S" "T" "f1") (seq "T" "E" "f2") (cseq "T" "E2" "f3" "x")))

(assert-equal "a task with a default flow and an unconditional flow"
              '((missing-condition "f3" "a flow out of the split T has no condition and is not its default"))
              (lint start (node "task" "T" " default=\"f2\"") end (node "endEvent" "E2")
                    (seq "S" "T" "f1") (seq "T" "E" "f2") (seq "T" "E2" "f3")))

(assert-equal "a parallel gateway split is explicit"
              '()
              (lint start (node "parallelGateway" "F") (node "task" "A") (node "task" "B")
                    (node "parallelGateway" "J") end
                    (seq "S" "F" "f1") (seq "F" "A" "f2") (seq "F" "B" "f3")
                    (seq "A" "J" "f4") (seq "B" "J" "f5") (seq "J" "E" "f6")))

;; ===================================================================
(display "Test group: missing-condition") (newline)

(define (two-way-split kind default second-flow)
  (lint start (node kind "G" default) (node "task" "A") (node "task" "B") end
        (seq "S" "G" "f1") (cseq "G" "A" "f2" "x") second-flow
        (seq "A" "E" "f4") (seq "B" "E" "f5")))

(assert-equal "an exclusive split flow with no condition"
              '((missing-condition "f3" "a flow out of the split G has no condition and is not its default"))
              (two-way-split "exclusiveGateway" "" (seq "G" "B" "f3")))

(assert-equal "an inclusive split flow with no condition"
              '((missing-condition "f3" "a flow out of the split G has no condition and is not its default"))
              (two-way-split "inclusiveGateway" "" (seq "G" "B" "f3")))

(assert-equal "an empty condition counts as none"
              '((missing-condition "f3" "a flow out of the split G has no condition and is not its default"))
              (two-way-split "exclusiveGateway" "" (cseq "G" "B" "f3" "  ")))

(assert-equal "the default flow needs no condition"
              '()
              (two-way-split "exclusiveGateway" " default=\"f3\"" (seq "G" "B" "f3")))

(assert-equal "every flow of a split with conditions"
              '()
              (two-way-split "inclusiveGateway" "" (cseq "G" "B" "f3" "y")))

(assert-equal "a parallel split needs no conditions"
              '()
              (lint start (node "parallelGateway" "G") (node "task" "A") (node "task" "B")
                    (node "parallelGateway" "J") end
                    (seq "S" "G" "f1") (seq "G" "A" "f2") (seq "G" "B" "f3")
                    (seq "A" "J" "f4") (seq "B" "J" "f5") (seq "J" "E" "f6")))

(assert-equal "a parallel split with one conditional flow"
              '((missing-condition "f3" "a flow out of the split G has no condition and is not its default"))
              (two-way-split "parallelGateway" "" (seq "G" "B" "f3")))

(assert-equal "every flow without a condition is reported, in document order"
              '((missing-condition "f2" "a flow out of the split G has no condition and is not its default")
                (missing-condition "f4" "a flow out of the split G has no condition and is not its default"))
              (lint start (node "exclusiveGateway" "G") (node "task" "A") (node "task" "B") (node "task" "C") end
                    (seq "S" "G" "f1") (seq "G" "A" "f2") (cseq "G" "B" "f3" "x") (seq "G" "C" "f4")
                    (seq "A" "E" "f5") (seq "B" "E" "f6") (seq "C" "E" "f7")))

(assert-equal "a default attribute on another node does not exempt a flow"
              '((missing-condition "f3" "a flow out of the split G has no condition and is not its default"))
              (lint start (node "exclusiveGateway" "G") (node "task" "A") (node "task" "B" " default=\"f3\"") end
                    (seq "S" "G" "f1") (cseq "G" "A" "f2" "x") (seq "G" "B" "f3")
                    (seq "A" "E" "f4") (seq "B" "E" "f5")))

(assert-equal "an exclusive gateway with one outgoing flow needs no condition"
              '()
              (lint start (node "task" "T") (node "exclusiveGateway" "M") end
                    (seq "S" "T" "f1") (seq "T" "M" "f2") (seq "M" "E" "f3")))

;; ===================================================================
(display "Test group: gateway-join-fork") (newline)

(define (repeat n thunk)
  (if (= n 0) '() (let ((x (thunk))) (cons x (repeat (- n 1) thunk)))))

(define (gateway-in-out ins outs)
  (let ((flow-id 0))
    (define (next-id) (set! flow-id (+ flow-id 1)) (string-append "f" (number->string flow-id)))
    (apply lint start (node "parallelGateway" "F") (node "parallelGateway" "G") (node "parallelGateway" "J") end
           (append
            (list (seq "S" "F" (next-id)))
            (repeat ins (lambda () (seq "F" "G" (next-id))))
            (repeat outs (lambda () (seq "G" "J" (next-id))))
            (list (seq "J" "E" (next-id)))))))

(assert-equal "a gateway that joins two flows and forks two"
              '((gateway-join-fork "G" "the gateway both joins and forks"))
              (filter (lambda (v) (eq? (car v) 'gateway-join-fork)) (gateway-in-out 2 2)))

(assert-equal "a gateway that only joins"
              '()
              (filter (lambda (v) (eq? (car v) 'gateway-join-fork)) (gateway-in-out 2 1)))

(assert-equal "a gateway that only forks"
              '()
              (filter (lambda (v) (eq? (car v) 'gateway-join-fork)) (gateway-in-out 1 2)))

(assert-equal "an exclusive gateway that joins and forks"
              '((gateway-join-fork "M" "the gateway both joins and forks"))
              (lint start (node "parallelGateway" "F") (node "task" "A") (node "task" "B")
                    (node "exclusiveGateway" "M") end (node "endEvent" "E2")
                    (seq "S" "F" "f1") (seq "F" "A" "f2") (seq "F" "B" "f3") (seq "A" "M" "f4") (seq "B" "M" "f5")
                    (cseq "M" "E" "f6" "x") (cseq "M" "E2" "f7" "y")))

(assert-equal "a task that joins and forks is not a gateway"
              '((implicit-split "T" "more than one outgoing flow without a condition"))
              (lint start (node "parallelGateway" "F") (node "task" "A") (node "task" "B")
                    (node "task" "T") end (node "endEvent" "E2")
                    (seq "S" "F" "f1") (seq "F" "A" "f2") (seq "F" "B" "f3") (seq "A" "T" "f4")
                    (seq "B" "T" "f5") (seq "T" "E" "f6") (seq "T" "E2" "f7")))

;; ===================================================================
(display "Test group: duplicate-flow") (newline)

(assert-equal "two flows with the same source and target"
              '((duplicate-flow "f3" "same source, target and condition as f2"))
              (lint start (node "parallelGateway" "F") (node "parallelGateway" "J") end
                    (seq "S" "F" "f1") (seq "F" "J" "f2") (seq "F" "J" "f3") (seq "J" "E" "f4")))

(assert-equal "three flows with the same source and target"
              '((duplicate-flow "f3" "same source, target and condition as f2")
                (duplicate-flow "f4" "same source, target and condition as f2"))
              (lint start (node "parallelGateway" "F") (node "parallelGateway" "J") end
                    (seq "S" "F" "f1") (seq "F" "J" "f2") (seq "F" "J" "f3") (seq "F" "J" "f4")
                    (seq "J" "E" "f5")))

(assert-equal "the same source and target with different conditions"
              '()
              (lint start (node "exclusiveGateway" "G") (node "exclusiveGateway" "M") end
                    (seq "S" "G" "f1") (cseq "G" "M" "f2" "x") (cseq "G" "M" "f3" "y") (seq "M" "E" "f4")))

(assert-equal "the same source and condition with different targets"
              '()
              (lint start (node "inclusiveGateway" "G") (node "task" "A") (node "task" "B")
                    (node "inclusiveGateway" "J") end
                    (seq "S" "G" "f1") (cseq "G" "A" "f2" "x") (cseq "G" "B" "f3" "x")
                    (seq "A" "J" "f4") (seq "B" "J" "f5") (seq "J" "E" "f6")))

(assert-equal "the same target and condition from different sources"
              '()
              (lint start (node "parallelGateway" "F") (node "task" "A") (node "task" "B")
                    (node "parallelGateway" "J") end
                    (seq "S" "F" "f1") (seq "F" "A" "f2") (seq "F" "B" "f3")
                    (seq "A" "J" "f4") (seq "B" "J" "f5") (seq "J" "E" "f6")))

;; ===================================================================
(display "Test group: order") (newline)

(assert-equal "violations come grouped by check, then in document order"
              '((no-end-event "P" "the process has no end event")
                (disconnected "B" "no outgoing flow")
                (disconnected "A" "no outgoing flow")
                (implicit-split "S" "more than one outgoing flow without a condition"))
              (lint start (node "task" "B") (node "task" "A")
                    (seq "S" "B" "f1") (seq "S" "A" "f2")))

(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)

(when (> fail-count 0)
  (exit 1))
