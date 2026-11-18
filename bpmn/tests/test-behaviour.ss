;; test-behaviour.ss
;; Tests for the BPMN behaviour check: the state explorer and its violations
;; (HC-63).
;;
;; Run with: scheme --libdirs ../src --program test-behaviour.ss

(import (rnrs) (bpmn model) (bpmn behaviour))

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

(define (as-lists vs)
  (map (lambda (v) (list (bpmn-violation-kind v) (bpmn-violation-id v) (bpmn-violation-detail v))) vs))

;; The behaviour violations of a chart, as (kind id detail) lists.
(define (behave . body)
  (as-lists (bpmn-behaviour (bpmn-read-string (chart (apply string-append body))))))
;; The same with a state limit of LIMIT.
(define (behave-limit limit . body)
  (as-lists (bpmn-behaviour (bpmn-read-string (chart (apply string-append body))) limit)))

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
(display "Test group: sound charts") (newline)

(assert-equal "a sequence of tasks"
              '()
              (behave start (node "task" "T") end (seq "S" "T" "f1") (seq "T" "E" "f2")))

(assert-equal "an exclusive split closed by an exclusive join"
              '()
              (behave start (node "exclusiveGateway" "G" " default=\"fb\"") (node "task" "A") (node "task" "B")
                      (node "exclusiveGateway" "M") end
                      (seq "S" "G" "f1") (cseq "G" "A" "fa" "x") (seq "G" "B" "fb")
                      (seq "A" "M" "fa2") (seq "B" "M" "fb2") (seq "M" "E" "f2")))

(assert-equal "a parallel split closed by a parallel join"
              '()
              (behave start (node "parallelGateway" "G") (node "task" "A") (node "task" "B")
                      (node "parallelGateway" "J") end
                      (seq "S" "G" "f1") (seq "G" "A" "fa") (seq "G" "B" "fb")
                      (seq "A" "J" "fa2") (seq "B" "J" "fb2") (seq "J" "E" "f2")))

(assert-equal "an inclusive split closed by an inclusive join"
              '()
              (behave start (node "inclusiveGateway" "G") (node "task" "A") (node "task" "B")
                      (node "inclusiveGateway" "J") end
                      (seq "S" "G" "f1") (cseq "G" "A" "fa" "x") (cseq "G" "B" "fb" "y")
                      (seq "A" "J" "fa2") (seq "B" "J" "fb2") (seq "J" "E" "f2")))

(assert-equal "an inclusive join waits for a token still upstream of an empty incoming flow"
              '()
              (behave start (node "parallelGateway" "G") (node "task" "A") (node "task" "B")
                      (node "task" "B2") (node "inclusiveGateway" "J") end
                      (seq "S" "G" "f1") (seq "G" "A" "fa") (seq "G" "B" "fb") (seq "B" "B2" "fb1")
                      (seq "A" "J" "fa2") (seq "B2" "J" "fb2") (seq "J" "E" "f2")))

(assert-equal "a loop with an exit"
              '()
              (behave start (node "exclusiveGateway" "M") (node "task" "A") (node "exclusiveGateway" "G")
                      end
                      (seq "S" "M" "f1") (seq "M" "A" "f2") (seq "A" "G" "f3")
                      (cseq "G" "M" "back" "again") (cseq "G" "E" "out" "done")))

(assert-equal "each start event begins its own run"
              '()
              (behave start (node "startEvent" "S2") (node "task" "T") (node "task" "T2") end
                      (seq "S" "T" "f1") (seq "S2" "T2" "f2") (seq "T" "E" "f3") (seq "T2" "E" "f4")))

(assert-equal "a chart with no start event is left to the lint"
              '()
              (behave (node "task" "T") end (seq "T" "E" "f1")))

;; ===================================================================
(display "Test group: dead tasks, dead flows and deadlock") (newline)

(assert-equal "an exclusive split closed by a parallel join deadlocks and kills what follows"
              '((deadlock "fa2" "no node can fire, with tokens on fa2")
                (deadlock "fb2" "no node can fire, with tokens on fb2")
                (dead-task "T" "the task never runs")
                (dead-flow "f2" "the flow never holds a token")
                (dead-flow "f3" "the flow never holds a token"))
              (behave start (node "exclusiveGateway" "G") (node "task" "A") (node "task" "B")
                      (node "parallelGateway" "J") (node "task" "T") end
                      (seq "S" "G" "f1") (cseq "G" "A" "fa" "x") (cseq "G" "B" "fb" "y")
                      (seq "A" "J" "fa2") (seq "B" "J" "fb2") (seq "J" "T" "f2") (seq "T" "E" "f3")))

;; ===================================================================
(display "Test group: unsafe flows") (newline)

(assert-equal "a parallel split closed by an exclusive join puts two tokens on one flow"
              '((unsafe-flow "fx" "a second token reaches the flow"))
              (behave start (node "parallelGateway" "G") (node "exclusiveGateway" "X") end
                      (seq "S" "G" "f1") (seq "G" "X" "fa") (seq "G" "X" "fb") (seq "X" "E" "fx")))

;; ===================================================================
(display "Test group: runs that cannot finish") (newline)

(assert-equal "a loop with no way out cannot complete"
              '((cannot-complete "f1" "no run can finish from tokens on f1"))
              (behave start (node "task" "A") (node "task" "B") end
                      (seq "S" "A" "f1") (seq "A" "B" "f2") (seq "B" "A" "f3")))

(assert-equal "only the point of no return is reported"
              '((cannot-complete "f3" "no run can finish from tokens on f3"))
              (behave start (node "task" "T") (node "exclusiveGateway" "G") (node "task" "A")
                      (node "task" "B") end
                      (seq "S" "T" "f1") (seq "T" "G" "f2") (cseq "G" "A" "f3" "x") (cseq "G" "E" "f4" "y")
                      (seq "A" "B" "f5") (seq "B" "A" "f6")))

;; ===================================================================
(display "Test group: splits and joins in detail") (newline)

(assert-equal "a blank condition is no condition, so that flow is always taken"
              '((deadlock "fb2" "no node can fire, with tokens on fb2"))
              (behave start (node "inclusiveGateway" "G") (node "task" "A") (node "task" "B")
                      (node "parallelGateway" "J") end
                      (seq "S" "G" "f1") (cseq "G" "A" "fa" "x") (cseq "G" "B" "fb" " ")
                      (seq "A" "J" "fa2") (seq "B" "J" "fb2") (seq "J" "E" "f2")))

(assert-equal "an inclusive join ignores a token that cannot reach it"
              '()
              (behave start (node "parallelGateway" "P") (node "inclusiveGateway" "J")
                      (node "parallelGateway" "Q") end
                      (seq "S" "P" "f1") (seq "P" "J" "fa") (seq "P" "Q" "fb")
                      (seq "J" "Q" "fj") (seq "Q" "E" "f2")))

;; The token on ft waits at Q for J's output. Q can reach J's empty incoming
;; flow fb through Z and B, but Q is also upstream of A, the source of the full
;; flow fa, so by BPMN's rule J fires rather than deadlocking with Q.
(assert-equal "an inclusive join does not wait for a token behind a full incoming flow"
              '((deadlock "fj" "no node can fire, with tokens on fj"))
              (behave start (node "parallelGateway" "P") (node "task" "A") (node "task" "B")
                      (node "inclusiveGateway" "J") (node "parallelGateway" "Q") (node "exclusiveGateway" "Z") end
                      (seq "S" "P" "f1") (seq "P" "A" "fpa") (seq "P" "Q" "ft")
                      (seq "A" "J" "fa") (seq "B" "J" "fb") (seq "J" "Q" "fj") (seq "Q" "Z" "fq")
                      (cseq "Z" "A" "fza" "x") (cseq "Z" "B" "fzb" "y") (cseq "Z" "E" "fze" "z")))

(assert-equal "an inclusive join inside a rework loop is sound"
              '()
              (behave start (node "exclusiveGateway" "M") (node "parallelGateway" "P") (node "task" "A")
                      (node "task" "B") (node "task" "B2") (node "inclusiveGateway" "J")
                      (node "exclusiveGateway" "X") end
                      (seq "S" "M" "f1") (seq "M" "P" "fm") (seq "P" "A" "fa") (seq "P" "B" "fb")
                      (seq "A" "J" "fa2") (seq "B" "B2" "fb1") (seq "B2" "J" "fb2") (seq "J" "X" "fj")
                      (cseq "X" "E" "out" "done") (cseq "X" "M" "back" "again")))

(assert-equal "an inclusive join waits for a token that loops back into an empty incoming flow"
              '()
              (behave start (node "parallelGateway" "P") (node "task" "A") (node "task" "L")
                      (node "exclusiveGateway" "X") (node "inclusiveGateway" "J") end
                      (seq "S" "P" "f1") (seq "P" "A" "fpa") (seq "P" "L" "fpl")
                      (seq "L" "X" "fl") (cseq "X" "L" "again" "x") (cseq "X" "J" "fb" "y")
                      (seq "A" "J" "fa") (seq "J" "E" "fj")))

(assert-equal "an inclusive split takes its default only when no condition holds"
              '((deadlock "fb2" "no node can fire, with tokens on fb2")
                (deadlock "fa2" "no node can fire, with tokens on fa2")
                (dead-flow "f2" "the flow never holds a token"))
              (behave start (node "inclusiveGateway" "G" " default=\"fb\"") (node "task" "A") (node "task" "B")
                      (node "parallelGateway" "J") end
                      (seq "S" "G" "f1") (cseq "G" "A" "fa" "x") (seq "G" "B" "fb")
                      (seq "A" "J" "fa2") (seq "B" "J" "fb2") (seq "J" "E" "f2")))

(assert-equal "a chart that makes tokens without end stops at the first unsafe flow"
              '((unsafe-flow "fe" "a second token reaches the flow"))
              (behave start (node "task" "T") (node "parallelGateway" "P") end
                      (seq "S" "T" "f1") (seq "T" "P" "ft") (seq "P" "T" "fback") (seq "P" "E" "fe")))

;; The search from the token on fc must stop at nodes it has seen, or it would
;; circle C1 and C2 for ever.
(assert-equal "an inclusive join's search for upstream tokens ends in a cycle"
              '((cannot-complete "f1" "no run can finish from tokens on f1"))
              (behave start (node "startEvent" "S2") (node "parallelGateway" "P") (node "task" "A")
                      (node "task" "C1") (node "task" "C2") (node "task" "B")
                      (node "inclusiveGateway" "J") end
                      (seq "S" "P" "f1") (seq "P" "A" "fpa") (seq "P" "C1" "fc")
                      (seq "C1" "C2" "fc1") (seq "C2" "C1" "fc2")
                      (seq "S2" "B" "fsb") (seq "A" "J" "fa") (seq "B" "J" "fb") (seq "J" "E" "fj")))

;; ===================================================================
(display "Test group: state limit") (newline)

(define parallel-chart
  (list start (node "parallelGateway" "G") (node "task" "A") (node "task" "B")
        (node "parallelGateway" "J") end
        (seq "S" "G" "f1") (seq "G" "A" "fa") (seq "G" "B" "fb")
        (seq "A" "J" "fa2") (seq "B" "J" "fb2") (seq "J" "E" "f2")))

;; The chart has seven states: f1; fa fb; fa2 fb; fa fb2; fa2 fb2; f2; none.
(assert-equal "one state more than the limit stops with state-limit"
              '((state-limit "P" "more than 6 states"))
              (apply behave-limit 6 parallel-chart))

(assert-equal "exactly the limit's number of states is within it"
              '()
              (apply behave-limit 7 parallel-chart))

(assert-equal "the default state limit is the plan's 100,000"
              100000
              bpmn-default-state-limit)

(newline)
(display "Passed: ") (display pass-count) (display ", failed: ") (display fail-count) (newline)
(exit (if (= fail-count 0) 0 1))
