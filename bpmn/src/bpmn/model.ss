;; model.ss
;; The BPMN model the checks run on: one process, its flow nodes and sequence
;; flows, with embedded sub-processes flattened into it (HC-61).
;;
;; The reader fails closed. An element it cannot reason about becomes an
;; unsupported-element violation rather than being skipped. Where such an
;; element is an activity it stays in the graph as one opaque task, and an event
;; with an event definition keeps its start or end kind, so later checks still
;; see a connected chart.

(library (bpmn model)
  (export bpmn-read-string bpmn-read-file bpmn-read-xml
          bpmn-model? bpmn-model-process-id bpmn-model-nodes bpmn-model-flows
          bpmn-model-data bpmn-model-violations
          bpmn-node? bpmn-node-id bpmn-node-kind bpmn-node-name bpmn-node-xml
          bpmn-flow? bpmn-flow-id bpmn-flow-source bpmn-flow-target
          bpmn-flow-condition bpmn-flow-default?
          bpmn-violation? make-bpmn-violation bpmn-violation-kind bpmn-violation-id
          bpmn-violation-detail
          bpmn-model-ns)
  (import (rnrs) (bpmn xml))

  ;; data holds the data declarations, as XML elements in document order:
  ;; itemDefinition, property, dataObject, dataObjectReference, ioSpecification.
  (define-record-type bpmn-model (fields process-id nodes flows data violations))
  ;; kind is one of task, start, end, exclusive, parallel, inclusive.
  (define-record-type bpmn-node (fields id kind name xml))
  ;; condition is the trimmed conditionExpression text, or #f.
  (define-record-type bpmn-flow (fields id source target condition default?))
  ;; id is the element's id, or #f when it has none.
  (define-record-type bpmn-violation (fields kind id detail))

  (define bpmn-model-ns "http://www.omg.org/spec/BPMN/20100524/MODEL")
  (define bpmn-di-ns "http://www.omg.org/spec/BPMN/20100524/DI")

  (define task-names
    '("task" "userTask" "serviceTask" "scriptTask" "manualTask" "businessRuleTask"
      "sendTask" "receiveTask"))
  (define gateway-kinds
    '(("exclusiveGateway" . exclusive) ("parallelGateway" . parallel) ("inclusiveGateway" . inclusive)))
  ;; Activities that are unsupported but still sit in the flow as one opaque task.
  (define opaque-activity-names '("callActivity" "transaction" "adHocSubProcess"))
  ;; Flow nodes that are unsupported and approximated by the nearest supported kind.
  (define approximated-nodes
    '(("eventBasedGateway" . exclusive) ("complexGateway" . inclusive)
      ("intermediateCatchEvent" . task) ("intermediateThrowEvent" . task)))
  (define (flow-node-name? name)
    (or (member name task-names) (assoc name gateway-kinds) (member name opaque-activity-names)
        (assoc name approximated-nodes) (member name '("startEvent" "endEvent" "subProcess"))))
  ;; Children that give an event a trigger or result, so it is not a none event.
  (define event-definition-names
    '("messageEventDefinition" "timerEventDefinition" "errorEventDefinition"
      "escalationEventDefinition" "cancelEventDefinition" "compensateEventDefinition"
      "conditionalEventDefinition" "linkEventDefinition" "signalEventDefinition"
      "terminateEventDefinition" "eventDefinitionRef"))
  (define data-names '("property" "dataObject" "dataObjectReference" "ioSpecification"))
  ;; Elements with no effect on how the process runs.
  (define decoration-names
    '("documentation" "extensionElements" "laneSet" "textAnnotation" "association" "group"))
  ;; Children of a flow node that are read elsewhere or have no effect on how it runs.
  (define node-child-names
    '("documentation" "extensionElements" "incoming" "outgoing"))
  (define task-child-names
    '("ioSpecification" "dataInputAssociation" "dataOutputAssociation" "property"
      "script" "rendering" "humanPerformer" "potentialOwner" "performer" "resourceRole"))
  ;; Children of a sub-process element that belong to the sub-process itself.
  (define sub-process-unsupported-names
    '("ioSpecification" "dataInputAssociation" "dataOutputAssociation"
      "multiInstanceLoopCharacteristics" "standardLoopCharacteristics"))
  (define definitions-ignored-names
    '("documentation" "extensionElements" "import" "message" "signal" "error" "escalation"
      "interface" "resource" "category" "eventDefinition" "timerEventDefinition"
      "messageEventDefinition" "signalEventDefinition" "errorEventDefinition"
      "escalationEventDefinition" "relationship" "partnerEntity" "partnerRole" "dataStore"))

  (define (bpmn? e) (equal? (xml-element-ns e) bpmn-model-ns))
  (define (bpmn-named? e name) (and (bpmn? e) (string=? (xml-element-name e) name)))
  (define (child-elements e) (filter xml-element? (xml-element-children e)))
  (define (event-definition? e)
    (and (bpmn? e) (member (xml-element-name e) event-definition-names) #t))
  (define (element-label e)
    (if (bpmn? e)
        (xml-element-name e)
        (string-append (or (xml-element-ns e) "") " " (xml-element-name e))))

  (define (trim s)
    (let* ((n (string-length s))
           (start (let loop ((k 0)) (if (and (< k n) (char-whitespace? (string-ref s k))) (loop (+ k 1)) k)))
           (end (let loop ((k n)) (if (and (> k start) (char-whitespace? (string-ref s (- k 1)))) (loop (- k 1)) k))))
      (substring s start end)))

  (define (bpmn-read-string s) (bpmn-read-xml (xml-read-string s)))
  (define (bpmn-read-file path) (bpmn-read-xml (xml-read-file path)))

  (define (bpmn-read-xml root)
    (unless (bpmn-named? root "definitions")
      (error 'bpmn-read "root is not a BPMN definitions element"))
    ;; Everything is accumulated in reverse and reversed once at the end.
    (let ((nodes '()) (flow-elts '()) (data '()) (violations '())
          (seen-ids '()) (process-id #f)
          ;; sub-process id -> (inner start id . inner end id)
          (rewire '()))

      (define (report! id detail)
        (set! violations (cons (make-bpmn-violation 'unsupported-element id detail) violations)))

      ;; Register E's id; report and return #f when it is missing or taken.
      (define (claim-id! e)
        (let ((id (xml-attr e "id")))
          (cond
            ((not id) (report! #f (string-append (element-label e) " without an id")) #f)
            ((member id seen-ids) (report! id (string-append (element-label e) ": duplicate id")) #f)
            (else (set! seen-ids (cons id seen-ids)) id))))

      (define (add-node! id kind e)
        (set! nodes (cons (make-bpmn-node id kind (xml-attr e "name") e) nodes)))

      ;; Report each child of flow node E that is not in ALLOWED. Event
      ;; definitions are named by their own element.
      (define (check-children! id e allowed)
        (for-each
         (lambda (c)
           (cond
             ((and (bpmn? c) (member (xml-element-name c) allowed))
              (when (member (xml-element-name c) '("dataInputAssociation" "dataOutputAssociation"))
                (when (exists (lambda (x) (bpmn-named? x "transformation")) (child-elements c))
                  (report! id (string-append (xml-element-name c) " transformation")))))
             (else (report! id (string-append (xml-element-name e) " " (element-label c))))))
         (child-elements e)))

      (define (none-event? e)
        (not (exists event-definition? (child-elements e))))

      (define (read-event! e kind)
        (let ((id (claim-id! e)))
          (when id
            (check-children! id e node-child-names)
            (add-node! id kind e))))

      ;; One token at a time runs through KIDS when every node but START has an
      ;; incoming flow, every node but END has an outgoing flow, and only an
      ;; exclusive or event-based gateway has more than one outgoing flow.
      (define (single-token? kids start end)
        (let ((flows (filter (lambda (c) (bpmn-named? c "sequenceFlow")) kids)))
          (define (flow-count attr n)
            (length (filter (lambda (f) (equal? (xml-attr f attr) (xml-attr n "id"))) flows)))
          (for-all
           (lambda (n)
             (let ((name (xml-element-name n))
                   (in (flow-count "targetRef" n))
                   (out (flow-count "sourceRef" n)))
               (and (or (eq? n start) (> in 0))
                    (or (eq? n end) (> out 0))
                    (or (<= out 1) (member name '("exclusiveGateway" "eventBasedGateway")))
                    (not (member name '("parallelGateway" "inclusiveGateway" "complexGateway"))))))
           (filter (lambda (c) (and (bpmn? c) (flow-node-name? (xml-element-name c)))) kids))))

      ;; A sub-process flattens when it has exactly one none start event and
      ;; one none end event among its direct children, and that end event has at
      ;; most one incoming flow. Its inner start and end
      ;; become plain tasks that take the sub-process's incoming and outgoing flows.
      (define (read-sub-process! e)
        (let ((id (claim-id! e)))
          (when id
            (let* ((kids (child-elements e))
                   (starts (filter (lambda (c) (bpmn-named? c "startEvent")) kids))
                   (ends (filter (lambda (c) (bpmn-named? c "endEvent")) kids)))
              (cond
                ((equal? (xml-attr e "triggeredByEvent") "true")
                 (report! id "subProcess triggeredByEvent"))
                ((not (and (= (length starts) 1) (= (length ends) 1)
                           (none-event? (car starts)) (none-event? (car ends))
                           (xml-attr (car starts) "id") (xml-attr (car ends) "id")))
                 (report! id "subProcess: needs exactly one none start event and one none end event")
                 (add-node! id 'task e))
                ;; Its end event completes the sub-process once, however many tokens
                ;; reach it; as a task it would pass each of them on.
                ((> (length (filter (lambda (c) (and (bpmn-named? c "sequenceFlow")
                                                     (equal? (xml-attr c "targetRef") (xml-attr (car ends) "id"))))
                                    kids))
                    1)
                 (report! id "subProcess: its end event has more than one incoming flow")
                 (add-node! id 'task e))
                ;; It completes only when every token inside it has finished, which a
                ;; flattened graph cannot express unless one token runs at a time.
                ((not (single-token? kids (car starts) (car ends)))
                 (report! id "subProcess: more than one token can run inside it")
                 (add-node! id 'task e))
                (else
                 (for-each
                  (lambda (c)
                    (when (and (bpmn? c) (member (xml-element-name c) sub-process-unsupported-names))
                      (report! id (string-append "subProcess " (xml-element-name c)))))
                  kids)
                 (set! rewire (cons (list id (xml-attr (car starts) "id") (xml-attr (car ends) "id")) rewire))
                 (read-container! e (lambda (c) (or (memq c starts) (memq c ends))))))))))

      ;; Read the flow elements of a process or sub-process. INNER-EVENT? picks
      ;; out a sub-process's own start and end event, which become tasks.
      (define (read-container! container inner-event?)
        (for-each
         (lambda (c)
           (let ((name (xml-element-name c)))
             (cond
               ((and (bpmn-named? container "subProcess")
                     (bpmn? c)
                     (member name (append node-child-names sub-process-unsupported-names)))
                (values))
               ((not (bpmn? c))
                (report! (xml-attr c "id") (element-label c)))
               ((inner-event? c)
                (let ((id (claim-id! c)))
                  (when id
                    (check-children! id c node-child-names)
                    (add-node! id 'task c))))
               ((member name task-names)
                (let ((id (claim-id! c)))
                  (when id
                    (check-children! id c (append node-child-names task-child-names))
                    (add-node! id 'task c))))
               ((string=? name "startEvent") (read-event! c 'start))
               ((string=? name "endEvent") (read-event! c 'end))
               ((assoc name gateway-kinds)
                => (lambda (k)
                     (let ((id (claim-id! c)))
                       (when id
                         (check-children! id c node-child-names)
                         (add-node! id (cdr k) c)))))
               ((string=? name "subProcess") (read-sub-process! c))
               ((member name opaque-activity-names)
                (let ((id (claim-id! c)))
                  (when id
                    (report! id name)
                    (add-node! id 'task c))))
               ((assoc name approximated-nodes)
                => (lambda (k)
                     (let ((id (claim-id! c)))
                       (when id
                         (report! id name)
                         (add-node! id (cdr k) c)))))
               ((string=? name "sequenceFlow")
                (let ((id (claim-id! c)))
                  (when id
                    (for-each
                     (lambda (k)
                       (unless (and (bpmn? k)
                                    (member (xml-element-name k)
                                            '("conditionExpression" "documentation" "extensionElements")))
                         (report! id (string-append "sequenceFlow " (element-label k)))))
                     (child-elements c))
                    (if (and (xml-attr c "sourceRef") (xml-attr c "targetRef"))
                        (set! flow-elts (cons c flow-elts))
                        (report! id "sequenceFlow without sourceRef or targetRef")))))
               ((member name data-names) (set! data (cons c data)))
               ((member name decoration-names) (values))
               (else (report! (xml-attr c "id") name)))))
         (child-elements container)))

      ;; source id -> the flow its default attribute names, for every BPMN element
      ;; with both, sub-processes included.
      (define (default-attrs)
        (let loop ((e root) (acc '()))
          (fold-left (lambda (acc c)
                       (loop c (if (and (bpmn? c) (xml-attr c "id") (xml-attr c "default"))
                                   (cons (cons (xml-attr c "id") (xml-attr c "default")) acc)
                                   acc)))
                     acc (child-elements e))))

      ;; A flow is the default when its own source, before rewiring, names it in
      ;; a default attribute.
      (define (make-flow e defaults)
        (let* ((id (xml-attr e "id"))
               (source (let ((r (assoc (xml-attr e "sourceRef") rewire)))
                         (if r (caddr r) (xml-attr e "sourceRef"))))
               (target (let ((r (assoc (xml-attr e "targetRef") rewire)))
                         (if r (cadr r) (xml-attr e "targetRef"))))
               (cond-elt (find (lambda (k) (bpmn-named? k "conditionExpression")) (child-elements e))))
          (make-bpmn-flow id source target
                          (and cond-elt (trim (xml-text cond-elt)))
                          (let ((d (assoc (xml-attr e "sourceRef") defaults)))
                            (and d (string=? (cdr d) id))))))

      (for-each
       (lambda (c)
         (let ((name (xml-element-name c)))
           (cond
             ((equal? (xml-element-ns c) bpmn-di-ns) (values))
             ((not (bpmn? c)) (report! (xml-attr c "id") (element-label c)))
             ((string=? name "process")
              (if process-id
                  (report! (xml-attr c "id") "process: only one process is supported")
                  (begin
                    (set! process-id (or (xml-attr c "id") ""))
                    (read-container! c (lambda (x) #f)))))
             ((string=? name "itemDefinition") (set! data (cons c data)))
             ((member name definitions-ignored-names) (values))
             (else (report! (xml-attr c "id") name)))))
       (child-elements root))

      (set! nodes (reverse nodes))
      (let ((defaults (default-attrs)))
        (make-bpmn-model process-id
                         nodes
                         (map (lambda (e) (make-flow e defaults)) (reverse flow-elts))
                         (reverse data)
                         (reverse violations))))))
