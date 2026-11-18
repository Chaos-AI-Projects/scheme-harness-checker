;; test-model.ss
;; Tests for the BPMN model reader: elements, flattening, unsupported-element (HC-61).
;;
;; Run with: scheme --libdirs ../src --program test-model.ss

(import (rnrs) (bpmn xml) (bpmn model))

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

;; Wrap process content in a definitions element with the BPMN model namespace.
(define (chart process-body . extra-root)
  (string-append
   "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
   "<bpmn:definitions xmlns:bpmn=\"http://www.omg.org/spec/BPMN/20100524/MODEL\""
   " xmlns:bpmndi=\"http://www.omg.org/spec/BPMN/20100524/DI\""
   " xmlns:xsd=\"http://www.w3.org/2001/XMLSchema\" id=\"defs\">"
   (apply string-append extra-root)
   "<bpmn:process id=\"P\" isExecutable=\"true\">" process-body "</bpmn:process>"
   "<bpmndi:BPMNDiagram id=\"D\"><bpmndi:BPMNPlane id=\"DP\" bpmnElement=\"P\"/></bpmndi:BPMNDiagram>"
   "</bpmn:definitions>"))

(define (model-of process-body . extra-root)
  (bpmn-read-string (apply chart process-body extra-root)))

(define (node-summary m)
  (map (lambda (n) (list (bpmn-node-id n) (bpmn-node-kind n)))
       (bpmn-model-nodes m)))

(define (flow-summary m)
  (map (lambda (f) (list (bpmn-flow-id f) (bpmn-flow-source f) (bpmn-flow-target f)))
       (bpmn-model-flows m)))

(define (violation-summary m)
  (map (lambda (v) (list (bpmn-violation-kind v) (bpmn-violation-id v) (bpmn-violation-detail v)))
       (bpmn-model-violations m)))

(define (flow-by-id m id)
  (find (lambda (f) (string=? (bpmn-flow-id f) id)) (bpmn-model-flows m)))

(define (seq from to id) (string-append "<bpmn:sequenceFlow id=\"" id "\" sourceRef=\"" from "\" targetRef=\"" to "\"/>"))

;; ===================================================================
(display "Test group: a plain chart") (newline)

(define plain
  (model-of
   (string-append
    "<bpmn:startEvent id=\"S\" name=\"Begin\"/>"
    "<bpmn:userTask id=\"T\" name=\"Review\"/>"
    "<bpmn:exclusiveGateway id=\"G\" default=\"f3\"/>"
    "<bpmn:parallelGateway id=\"PG\"/>"
    "<bpmn:inclusiveGateway id=\"IG\"/>"
    "<bpmn:endEvent id=\"E\"/>"
    (seq "S" "T" "f1") (seq "T" "G" "f2") (seq "G" "E" "f3")
    "<bpmn:sequenceFlow id=\"f4\" sourceRef=\"G\" targetRef=\"PG\">"
    "<bpmn:conditionExpression xsi:type=\"tFormalExpression\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"><![CDATA[${x > 1}]]></bpmn:conditionExpression>"
    "</bpmn:sequenceFlow>"
    (seq "PG" "IG" "f5") (seq "IG" "E" "f6"))))

(assert-equal "process id" "P" (bpmn-model-process-id plain))
(assert-equal "node kinds"
              '(("S" start) ("T" task) ("G" exclusive) ("PG" parallel) ("IG" inclusive) ("E" end))
              (node-summary plain))
(assert-equal "node name" "Review" (bpmn-node-name (cadr (bpmn-model-nodes plain))))
(assert-equal "unnamed node" #f (bpmn-node-name (caddr (bpmn-model-nodes plain))))
(assert-equal "flows" '(("f1" "S" "T") ("f2" "T" "G") ("f3" "G" "E") ("f4" "G" "PG") ("f5" "PG" "IG") ("f6" "IG" "E"))
              (flow-summary plain))
(assert-equal "condition text" "${x > 1}" (bpmn-flow-condition (flow-by-id plain "f4")))
(assert-equal "no condition" #f (bpmn-flow-condition (flow-by-id plain "f3")))
(assert-equal "default flow" #t (bpmn-flow-default? (flow-by-id plain "f3")))
(assert-equal "non-default flow" #f (bpmn-flow-default? (flow-by-id plain "f4")))
(assert-equal "no violations" '() (violation-summary plain))

(assert-equal "every task kind is a plain task"
              '(task task task task task task task task)
              (map bpmn-node-kind
                   (bpmn-model-nodes
                    (model-of (string-append
                               "<bpmn:task id=\"a\"/><bpmn:userTask id=\"b\"/><bpmn:serviceTask id=\"c\"/>"
                               "<bpmn:scriptTask id=\"d\"><bpmn:script>x</bpmn:script></bpmn:scriptTask>"
                               "<bpmn:manualTask id=\"e\"/><bpmn:businessRuleTask id=\"f\"/>"
                               "<bpmn:sendTask id=\"g\"/><bpmn:receiveTask id=\"h\"/>")))))

(assert-equal "a task's default flow is marked"
              #t
              (bpmn-flow-default?
               (flow-by-id (model-of (string-append "<bpmn:task id=\"T\" default=\"f1\"/><bpmn:endEvent id=\"E\"/>"
                                                    (seq "T" "E" "f1")))
                           "f1")))

;; ===================================================================
(display "Test group: data declarations are kept") (newline)

(define data-model
  (model-of
   (string-append
    "<bpmn:property id=\"p1\" itemSubjectRef=\"i1\"/>"
    "<bpmn:dataObject id=\"do1\" itemSubjectRef=\"i1\"/>"
    "<bpmn:dataObjectReference id=\"dr1\" dataObjectRef=\"do1\"/>"
    "<bpmn:task id=\"T\">"
    "<bpmn:ioSpecification id=\"io\"><bpmn:dataInput id=\"in1\" itemSubjectRef=\"i1\"/>"
    "<bpmn:inputSet id=\"is\"><bpmn:dataInputRefs>in1</bpmn:dataInputRefs></bpmn:inputSet></bpmn:ioSpecification>"
    "<bpmn:dataInputAssociation id=\"a1\"><bpmn:sourceRef>dr1</bpmn:sourceRef><bpmn:targetRef>in1</bpmn:targetRef></bpmn:dataInputAssociation>"
    "</bpmn:task>")
   "<bpmn:itemDefinition id=\"i1\" structureRef=\"xsd:string\"/>"))

(assert-equal "data declarations in document order"
              '("itemDefinition" "property" "dataObject" "dataObjectReference")
              (map xml-element-name (bpmn-model-data data-model)))
(assert-equal "a task keeps its XML for the data checks"
              "ioSpecification"
              (xml-element-name (car (filter xml-element?
                                             (xml-element-children (bpmn-node-xml (car (bpmn-model-nodes data-model))))))))
(assert-equal "data declarations raise nothing" '() (violation-summary data-model))

;; ===================================================================
(display "Test group: non-executable decoration is ignored") (newline)

(assert-equal "annotations, lanes, documentation, extensions"
              '()
              (violation-summary
               (model-of
                (string-append
                 "<bpmn:documentation>doc</bpmn:documentation>"
                 "<bpmn:extensionElements><x:y xmlns:x=\"urn:x\"/></bpmn:extensionElements>"
                 "<bpmn:laneSet id=\"ls\"><bpmn:lane id=\"l\"><bpmn:flowNodeRef>T</bpmn:flowNodeRef></bpmn:lane></bpmn:laneSet>"
                 "<bpmn:task id=\"T\"><bpmn:documentation>d</bpmn:documentation><bpmn:incoming>f</bpmn:incoming></bpmn:task>"
                 "<bpmn:textAnnotation id=\"ta\"><bpmn:text>note</bpmn:text></bpmn:textAnnotation>"
                 "<bpmn:association id=\"as\" sourceRef=\"T\" targetRef=\"ta\"/>"
                 "<bpmn:group id=\"g\"/>")
                "<bpmn:message id=\"m\"/><bpmn:signal id=\"s\"/><bpmn:error id=\"e\"/>")))

;; ===================================================================
(display "Test group: sub-processes are flattened") (newline)

(define flat
  (model-of
   (string-append
    "<bpmn:startEvent id=\"S\"/>"
    "<bpmn:subProcess id=\"SP\"><bpmn:incoming>f1</bpmn:incoming><bpmn:outgoing>f2</bpmn:outgoing>"
    "<bpmn:startEvent id=\"SS\"/><bpmn:task id=\"ST\"/><bpmn:endEvent id=\"SE\"/>"
    (seq "SS" "ST" "s1") (seq "ST" "SE" "s2")
    "</bpmn:subProcess>"
    "<bpmn:endEvent id=\"E\"/>"
    "<bpmn:sequenceFlow id=\"f2\" sourceRef=\"SP\" targetRef=\"E\"><bpmn:conditionExpression>ok</bpmn:conditionExpression></bpmn:sequenceFlow>"
    (seq "S" "SP" "f1"))))

(assert-equal "inner start and end become plain tasks, sub-process node is gone"
              '(("S" start) ("SS" task) ("ST" task) ("SE" task) ("E" end))
              (node-summary flat))
(assert-equal "flows into and out of the sub-process are rewired"
              '(("s1" "SS" "ST") ("s2" "ST" "SE") ("f2" "SE" "E") ("f1" "S" "SS"))
              (flow-summary flat))
(assert-equal "a rewired flow keeps its condition" "ok" (bpmn-flow-condition (flow-by-id flat "f2")))
(assert-equal "flattening raises nothing" '() (violation-summary flat))

(define nested
  (model-of
   (string-append
    "<bpmn:startEvent id=\"S\"/>"
    "<bpmn:subProcess id=\"A\"><bpmn:startEvent id=\"AS\"/>"
    "<bpmn:subProcess id=\"B\"><bpmn:startEvent id=\"BS\"/><bpmn:endEvent id=\"BE\"/>" (seq "BS" "BE" "b1") "</bpmn:subProcess>"
    "<bpmn:endEvent id=\"AE\"/>" (seq "AS" "B" "a1") (seq "B" "AE" "a2")
    "</bpmn:subProcess>"
    "<bpmn:endEvent id=\"E\"/>" (seq "S" "A" "f1") (seq "A" "E" "f2"))))

(assert-equal "nested sub-processes flatten all the way"
              '(("S" start) ("AS" task) ("BS" task) ("BE" task) ("AE" task) ("E" end))
              (node-summary nested))
(assert-equal "nested flows rewired"
              '(("b1" "BS" "BE") ("a1" "AS" "BS") ("a2" "BE" "AE") ("f1" "S" "AS") ("f2" "AE" "E"))
              (flow-summary nested))

(define two-ends
  (model-of
   (string-append
    "<bpmn:startEvent id=\"S\"/>"
    "<bpmn:subProcess id=\"SP\"><bpmn:startEvent id=\"SS\"/><bpmn:endEvent id=\"E1\"/><bpmn:endEvent id=\"E2\"/>"
    (seq "SS" "E1" "s1") (seq "SS" "E2" "s2") "</bpmn:subProcess>"
    "<bpmn:endEvent id=\"E\"/>" (seq "S" "SP" "f1") (seq "SP" "E" "f2"))))

(assert-equal "a sub-process without exactly one start and one end is unsupported"
              '((unsupported-element "SP" "subProcess: needs exactly one none start event and one none end event"))
              (violation-summary two-ends))
(assert-equal "an unsupported sub-process stays one opaque task"
              '(("S" start) ("SP" task) ("E" end))
              (node-summary two-ends))
(assert-equal "flows of an unsupported sub-process keep their ends"
              '(("f1" "S" "SP") ("f2" "SP" "E"))
              (flow-summary two-ends))

(assert-equal "a sub-process's default flow is marked after rewiring"
              '(#t #f)
              (let ((m (model-of
                        (string-append
                         "<bpmn:subProcess id=\"SP\" default=\"f1\"><bpmn:startEvent id=\"SS\"/><bpmn:endEvent id=\"SE\"/>"
                         (seq "SS" "SE" "s1") "</bpmn:subProcess>"
                         "<bpmn:endEvent id=\"E\"/>" (seq "SP" "E" "f1") (seq "SP" "E" "f2")))))
                (list (bpmn-flow-default? (flow-by-id m "f1")) (bpmn-flow-default? (flow-by-id m "f2")))))
(assert-equal "a flattened sub-process with its own data or loop is unsupported"
              '((unsupported-element "SP" "subProcess ioSpecification")
                (unsupported-element "SP" "subProcess standardLoopCharacteristics"))
              (violation-summary
               (model-of
                (string-append
                 "<bpmn:subProcess id=\"SP\"><bpmn:ioSpecification/><bpmn:standardLoopCharacteristics/>"
                 "<bpmn:startEvent id=\"SS\"/><bpmn:endEvent id=\"SE\"/>" (seq "SS" "SE" "s1") "</bpmn:subProcess>"))))
(assert-equal "a sub-process whose inner start has no id is unsupported"
              '((unsupported-element "SP" "subProcess: needs exactly one none start event and one none end event"))
              (violation-summary
               (model-of "<bpmn:subProcess id=\"SP\"><bpmn:startEvent/><bpmn:endEvent id=\"SE\"/></bpmn:subProcess>")))
(assert-equal "a timer start inside a sub-process stops flattening"
              '((unsupported-element "SP" "subProcess: needs exactly one none start event and one none end event"))
              (violation-summary
               (model-of "<bpmn:subProcess id=\"SP\"><bpmn:startEvent id=\"SS\"><bpmn:timerEventDefinition/></bpmn:startEvent><bpmn:endEvent id=\"SE\"/></bpmn:subProcess>")))
(assert-equal "an event sub-process is unsupported"
              '((unsupported-element "ESP" "subProcess triggeredByEvent"))
              (violation-summary
               (model-of "<bpmn:subProcess id=\"ESP\" triggeredByEvent=\"true\"><bpmn:startEvent id=\"x\"/><bpmn:endEvent id=\"y\"/></bpmn:subProcess>")))

;; ===================================================================
(display "Test group: unsupported elements are reported, not skipped") (newline)

(define (unsupported-in process-body . extra-root)
  (violation-summary (apply model-of process-body extra-root)))

(assert-equal "boundary event"
              '((unsupported-element "b" "boundaryEvent"))
              (unsupported-in "<bpmn:task id=\"T\"/><bpmn:boundaryEvent id=\"b\" attachedToRef=\"T\"/>"))
(assert-equal "call activity"
              '((unsupported-element "c" "callActivity"))
              (unsupported-in "<bpmn:callActivity id=\"c\"/>"))
(assert-equal "event-based gateway"
              '((unsupported-element "g" "eventBasedGateway"))
              (unsupported-in "<bpmn:eventBasedGateway id=\"g\"/>"))
(assert-equal "complex gateway"
              '((unsupported-element "g" "complexGateway"))
              (unsupported-in "<bpmn:complexGateway id=\"g\"/>"))
(assert-equal "intermediate events"
              '((unsupported-element "i" "intermediateCatchEvent") (unsupported-element "j" "intermediateThrowEvent"))
              (unsupported-in "<bpmn:intermediateCatchEvent id=\"i\"/><bpmn:intermediateThrowEvent id=\"j\"/>"))
(assert-equal "timer start event"
              '((unsupported-element "S" "startEvent timerEventDefinition"))
              (unsupported-in "<bpmn:startEvent id=\"S\"><bpmn:timerEventDefinition/></bpmn:startEvent>"))
(assert-equal "terminate end event"
              '((unsupported-element "E" "endEvent terminateEventDefinition"))
              (unsupported-in "<bpmn:endEvent id=\"E\"><bpmn:terminateEventDefinition/></bpmn:endEvent>"))
(assert-equal "message end event"
              '((unsupported-element "E" "endEvent messageEventDefinition"))
              (unsupported-in "<bpmn:endEvent id=\"E\"><bpmn:messageEventDefinition/></bpmn:endEvent>"))
(assert-equal "multi-instance task"
              '((unsupported-element "T" "userTask multiInstanceLoopCharacteristics"))
              (unsupported-in "<bpmn:userTask id=\"T\"><bpmn:multiInstanceLoopCharacteristics/></bpmn:userTask>"))
(assert-equal "looping task"
              '((unsupported-element "T" "task standardLoopCharacteristics"))
              (unsupported-in "<bpmn:task id=\"T\"><bpmn:standardLoopCharacteristics/></bpmn:task>"))
(assert-equal "association with a transformation"
              '((unsupported-element "T" "dataInputAssociation transformation"))
              (unsupported-in
               (string-append
                "<bpmn:task id=\"T\"><bpmn:dataInputAssociation id=\"a\"><bpmn:sourceRef>x</bpmn:sourceRef>"
                "<bpmn:transformation>f(x)</bpmn:transformation></bpmn:dataInputAssociation></bpmn:task>")))
(assert-equal "data store reference"
              '((unsupported-element "ds" "dataStoreReference"))
              (unsupported-in "<bpmn:dataStoreReference id=\"ds\"/>"))
(assert-equal "transaction"
              '((unsupported-element "tx" "transaction"))
              (unsupported-in "<bpmn:transaction id=\"tx\"/>"))
(assert-equal "vendor element outside extensionElements"
              '((unsupported-element "v" "urn:vendor thing"))
              (unsupported-in "<v:thing xmlns:v=\"urn:vendor\" id=\"v\"/>"))
(assert-equal "unsupported element inside a sub-process"
              '((unsupported-element "cb" "callActivity"))
              (unsupported-in
               (string-append "<bpmn:subProcess id=\"SP\"><bpmn:startEvent id=\"SS\"/><bpmn:callActivity id=\"cb\"/>"
                              "<bpmn:endEvent id=\"SE\"/>" (seq "SS" "cb" "s1") (seq "cb" "SE" "s2")
                              "</bpmn:subProcess>")))
(assert-equal "collaboration"
              '((unsupported-element "C" "collaboration"))
              (unsupported-in "" "<bpmn:collaboration id=\"C\"><bpmn:participant id=\"pa\" processRef=\"P\"/></bpmn:collaboration>"))
(let ((m (model-of "" "<bpmn:process id=\"P0\"/>")))
  (assert-equal "the first process in the document is the chart" "P0" (bpmn-model-process-id m))
  (assert-equal "a second process"
                '((unsupported-element "P" "process: only one process is supported"))
                (violation-summary m)))

;; ===================================================================
(display "Test group: the document itself") (newline)

(define (read-error str)
  (guard (e ((message-condition? e) (condition-message e)))
    (bpmn-read-string str)
    #f))

(assert-equal "root must be BPMN definitions"
              "root is not a BPMN definitions element"
              (read-error "<definitions/>"))
(assert-equal "no process gives an empty model"
              '(#f () ())
              (let ((m (bpmn-read-string
                        "<definitions xmlns=\"http://www.omg.org/spec/BPMN/20100524/MODEL\"/>")))
                (list (bpmn-model-process-id m) (bpmn-model-nodes m) (bpmn-model-flows m))))
(assert-equal "an element with no id is unsupported"
              '((unsupported-element #f "task without an id"))
              (unsupported-in "<bpmn:task/>"))
(assert-equal "a duplicate id is unsupported"
              '((unsupported-element "T" "task: duplicate id"))
              (unsupported-in "<bpmn:task id=\"T\"/><bpmn:task id=\"T\"/>"))
(assert-equal "a flow without both ends is unsupported"
              '((unsupported-element "f" "sequenceFlow without sourceRef or targetRef"))
              (unsupported-in "<bpmn:task id=\"T\"/><bpmn:sequenceFlow id=\"f\" sourceRef=\"T\"/>"))
(assert-equal "the fixture file reads cleanly"
              '(("S" start) ("T" task) ("E" end))
              (node-summary (bpmn-read-file "../fixtures/minimal.bpmn")))

(display "Test group: boundaries") (newline)

(define (condition-of text)
  (bpmn-flow-condition
   (flow-by-id (model-of (string-append
                          "<bpmn:startEvent id=\"S\"/><bpmn:endEvent id=\"E\"/>"
                          "<bpmn:sequenceFlow id=\"f1\" sourceRef=\"S\" targetRef=\"E\">"
                          "<bpmn:conditionExpression>" text "</bpmn:conditionExpression></bpmn:sequenceFlow>"))
               "f1")))
(assert-equal "an all-blank condition trims to empty" "" (condition-of "   "))
(assert-equal "one blank either side is trimmed" "x" (condition-of " x "))
(assert-equal "three blanks either side are trimmed" "x" (condition-of "   x   "))

(define (sub-process-with-start-child child)
  (model-of (string-append
             "<bpmn:subProcess id=\"SP\"><bpmn:startEvent id=\"SS\">" child "</bpmn:startEvent>"
             "<bpmn:endEvent id=\"SE\"/>" (seq "SS" "SE" "s1") "</bpmn:subProcess>")))
(assert-equal "a start event with an outgoing child is still a none event"
              '(("SS" task) ("SE" task))
              (node-summary (sub-process-with-start-child "<bpmn:outgoing>s1</bpmn:outgoing>")))
(let ((m (sub-process-with-start-child "<x:timerEventDefinition xmlns:x=\"urn:x\"/>")))
  (assert-equal "a foreign event definition does not stop flattening" '(("SS" task) ("SE" task))
                (node-summary m))
  (assert-equal "the foreign event definition is reported"
                '((unsupported-element "SS" "startEvent urn:x timerEventDefinition"))
                (violation-summary m)))
(for-each
 (lambda (def)
   (assert-equal (string-append "a " def " start event does not flatten")
                 '(("SP" task))
                 (node-summary (sub-process-with-start-child (string-append "<bpmn:" def "/>")))))
 '("messageEventDefinition" "signalEventDefinition" "conditionalEventDefinition" "eventDefinitionRef"))

(assert-equal "a foreign child of a sequence flow is reported, even one named like a BPMN child"
              '((unsupported-element "f1" "sequenceFlow urn:x documentation"))
              (violation-summary
               (model-of (string-append
                          "<bpmn:startEvent id=\"S\"/><bpmn:endEvent id=\"E\"/>"
                          "<bpmn:sequenceFlow id=\"f1\" sourceRef=\"S\" targetRef=\"E\"><x:documentation xmlns:x=\"urn:x\"/></bpmn:sequenceFlow>"))))
(assert-equal "a default attribute marks only a flow out of its own node" '(#f #f)
              (let ((m (model-of (string-append
                                  "<bpmn:startEvent id=\"S\"/><bpmn:task id=\"T\"/><bpmn:task id=\"U\" default=\"f2\"/>"
                                  "<bpmn:endEvent id=\"E\"/>"
                                  (seq "S" "T" "f1") (seq "T" "E" "f2") (seq "T" "U" "f3") (seq "U" "E" "f4")))))
                (list (bpmn-flow-default? (flow-by-id m "f2")) (bpmn-flow-default? (flow-by-id m "f4")))))
(assert-equal "a sub-process's default attribute marks only a flow out of the sub-process" #f
              (bpmn-flow-default?
               (flow-by-id (model-of
                            (string-append
                             "<bpmn:startEvent id=\"S\"/>"
                             "<bpmn:subProcess id=\"SP\" default=\"f1\"><bpmn:startEvent id=\"SS\"/><bpmn:endEvent id=\"SE\"/>"
                             (seq "SS" "SE" "s1") "</bpmn:subProcess>"
                             "<bpmn:endEvent id=\"E\"/>" (seq "S" "SP" "f1") (seq "SP" "E" "f2")))
                           "f1")))
(assert-equal "a flow out of a foreign element is not its default" #f
              (bpmn-flow-default?
               (flow-by-id (model-of (string-append
                                      "<bpmn:endEvent id=\"E\"/>" (seq "K" "E" "f1")
                                      "<x:k xmlns:x=\"urn:x\" id=\"K\" default=\"f1\"/>"))
                           "f1")))
(assert-equal "a default attribute on a foreign element marks no flow default" #f
              (bpmn-flow-default?
               (flow-by-id (model-of (string-append
                                      "<bpmn:startEvent id=\"S\"/><bpmn:endEvent id=\"E\"/>" (seq "S" "E" "f1")
                                      "<x:k xmlns:x=\"urn:x\" id=\"K\" default=\"f1\"/>"))
                           "f1")))

(let ((m (model-of (string-append
                    "<bpmn:subProcess id=\"SP\"><bpmn:startEvent id=\"SS\"/><bpmn:parallelGateway id=\"PG\"/>"
                    "<bpmn:task id=\"A\"/><bpmn:task id=\"B\"/><bpmn:endEvent id=\"SE\"/>"
                    (seq "SS" "PG" "s1") (seq "PG" "A" "s2") (seq "PG" "B" "s3") (seq "A" "SE" "s4") (seq "B" "SE" "s5")
                    "</bpmn:subProcess>"))))
  (assert-equal "a sub-process whose end event has two incoming flows is not flattened"
                '(("SP" task)) (node-summary m))
  (assert-equal "a sub-process whose end event has two incoming flows is reported"
                '((unsupported-element "SP" "subProcess: its end event has more than one incoming flow"))
                (violation-summary m)))

(define (sub-process-of inner)
  (model-of (string-append "<bpmn:subProcess id=\"SP\"><bpmn:startEvent id=\"SS\"/><bpmn:endEvent id=\"SE\"/>"
                           inner "</bpmn:subProcess>")))
(define single-token-refusal
  '((unsupported-element "SP" "subProcess: more than one token can run inside it")))
(for-each
 (lambda (case)
   (let ((m (sub-process-of (cadr case))))
     (assert-equal (string-append "a sub-process with " (car case) " is not flattened")
                   '(("SP" task)) (node-summary m))
     (assert-equal (string-append "a sub-process with " (car case) " is reported")
                   single-token-refusal (violation-summary m))))
 (list
  (list "an inner task that has no outgoing flow"
        (string-append "<bpmn:exclusiveGateway id=\"XG\"/><bpmn:task id=\"A\"/><bpmn:task id=\"W\"/>"
                       (seq "SS" "XG" "s1") (seq "XG" "A" "s2") (seq "XG" "W" "s3") (seq "A" "SE" "s4")))
  (list "an inner task that has no incoming flow"
        (string-append "<bpmn:task id=\"A\"/><bpmn:task id=\"W\"/>"
                       (seq "SS" "A" "s1") (seq "A" "SE" "s2") (seq "W" "A" "s3")))
  (list "a parallel split merged by an exclusive gateway"
        (string-append "<bpmn:parallelGateway id=\"PG\"/><bpmn:task id=\"A\"/><bpmn:task id=\"B\"/>"
                       "<bpmn:exclusiveGateway id=\"XM\"/>"
                       (seq "SS" "PG" "s1") (seq "PG" "A" "s2") (seq "PG" "B" "s3")
                       (seq "A" "XM" "s4") (seq "B" "XM" "s5") (seq "XM" "SE" "s6")))
  (list "an inclusive gateway"
        (string-append "<bpmn:inclusiveGateway id=\"IG\"/><bpmn:task id=\"A\"/>"
                       (seq "SS" "IG" "s1") (seq "IG" "A" "s2") (seq "A" "SE" "s3")))
  (list "a complex gateway"
        (string-append "<bpmn:complexGateway id=\"CG\"/><bpmn:task id=\"A\"/>"
                       (seq "SS" "CG" "s1") (seq "CG" "A" "s2") (seq "A" "SE" "s3")))
  (list "a task that splits into two flows"
        (string-append "<bpmn:task id=\"T\"/><bpmn:task id=\"A\"/><bpmn:task id=\"B\"/>"
                       "<bpmn:exclusiveGateway id=\"XM\"/>"
                       (seq "SS" "T" "s1") (seq "T" "A" "s2") (seq "T" "B" "s3")
                       (seq "A" "XM" "s4") (seq "B" "XM" "s5") (seq "XM" "SE" "s6")))
  (list "a start event that splits into two flows"
        (string-append "<bpmn:task id=\"A\"/><bpmn:task id=\"B\"/><bpmn:exclusiveGateway id=\"XM\"/>"
                       (seq "SS" "A" "s1") (seq "SS" "B" "s2")
                       (seq "A" "XM" "s3") (seq "B" "XM" "s4") (seq "XM" "SE" "s5")))))

(let ((m (sub-process-of
          (string-append "<bpmn:exclusiveGateway id=\"XG\"/><bpmn:eventBasedGateway id=\"EG\"/>"
                         "<bpmn:task id=\"A\"/><bpmn:task id=\"B\"/><bpmn:exclusiveGateway id=\"XM\"/>"
                         (seq "SS" "XG" "s1") (seq "XG" "A" "s2") (seq "XG" "EG" "s3") (seq "EG" "B" "s4")
                         (seq "A" "XM" "s5") (seq "B" "XM" "s6") (seq "XM" "SE" "s7")))))
  (assert-equal "a sub-process whose exclusive branches merge before its end is flattened"
                '(("SS" task) ("SE" task) ("XG" exclusive) ("EG" exclusive) ("A" task) ("B" task) ("XM" exclusive))
                (node-summary m))
  (assert-equal "a flattened sub-process reports only its approximated nodes"
                '((unsupported-element "EG" "eventBasedGateway"))
                (violation-summary m)))

(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)

(when (> fail-count 0)
  (exit 1))
