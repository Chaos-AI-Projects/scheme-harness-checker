;; xml.ss
;; A small XML reader for the subset a BPMN modeler saves (HC-61).
;;
;; It reads elements, attributes, namespaces, text, CDATA, comments, processing
;; instructions, and character and predefined entity references. A DTD is
;; rejected, so no entity can be defined and nothing is fetched. The encoding
;; declaration is ignored: input is read as UTF-8.

(library (bpmn xml)
  (export xml-read-string xml-read-port xml-read-file
          xml-element? xml-element-ns xml-element-name xml-element-attrs xml-element-children
          xml-attribute? xml-attribute-ns xml-attribute-name xml-attribute-value
          xml-attr xml-attr-ns xml-text)
  (import (rnrs))

  ;; ns is the namespace URI or #f; children holds elements and strings.
  (define-record-type xml-element (fields ns name attrs children))
  (define-record-type xml-attribute (fields ns name value))

  (define xml-ns-uri "http://www.w3.org/XML/1998/namespace")

  ;; The value of the attribute NAME that has no namespace, or #f.
  (define (xml-attr e name)
    (xml-attr-ns e #f name))

  (define (xml-attr-ns e ns name)
    (let ((a (find (lambda (a) (and (equal? (xml-attribute-ns a) ns)
                                    (string=? (xml-attribute-name a) name)))
                   (xml-element-attrs e))))
      (and a (xml-attribute-value a))))

  ;; The element's direct text, CDATA included, concatenated.
  (define (xml-text e)
    (apply string-append (filter string? (xml-element-children e))))

  (define (xml-read-port port)
    (let ((s (get-string-all port)))
      (xml-read-string (if (eof-object? s) "" s))))

  (define (xml-read-file path)
    (call-with-port (open-file-input-port path (file-options) (buffer-mode block) (native-transcoder))
      xml-read-port))

  (define (fail msg . irritants)
    (apply error 'xml-read msg irritants))

  (define (xml-read-string s)
    (define n (string-length s))
    (define i 0)

    (define (peek) (if (< i n) (string-ref s i) #f))
    (define (at? lit)
      (let ((k (string-length lit)))
        (and (<= (+ i k) n) (string=? (substring s i (+ i k)) lit))))
    ;; Advance past LIT and return #t when the input continues with it.
    (define (accept lit)
      (and (at? lit) (begin (set! i (+ i (string-length lit))) #t)))
    (define (expect lit)
      (if (at? lit)
          (set! i (+ i (string-length lit)))
          (fail (string-append "expected " lit) i)))
    (define (skip-ws)
      (when (and (peek) (char-whitespace? (peek)))
        (set! i (+ i 1))
        (skip-ws)))
    ;; Advance past the next occurrence of LIT, returning the text before it.
    (define (read-until lit what)
      (let ((k (string-length lit)))
        (let loop ((j i))
          (cond
            ((> (+ j k) n) (fail (string-append "unterminated " what) i))
            ((string=? (substring s j (+ j k)) lit)
             (let ((text (substring s i j)))
               (set! i (+ j k))
               text))
            (else (loop (+ j 1)))))))

    (define (name-char? c)
      (and c (or (char-alphabetic? c) (char-numeric? c)
                 (memv c '(#\- #\_ #\. #\:))
                 (> (char->integer c) 127))))
    (define (read-name)
      (let ((start i))
        (let loop ()
          (when (name-char? (peek))
            (set! i (+ i 1))
            (loop)))
        (when (= start i) (fail "expected a name" i))
        (substring s start i)))

    ;; Read an entity or character reference; i is just past the '&'.
    (define (read-reference)
      (let* ((body (read-until ";" "entity reference"))
             (len (string-length body)))
        (cond
          ((string=? body "lt") "<")
          ((string=? body "gt") ">")
          ((string=? body "amp") "&")
          ((string=? body "quot") "\"")
          ((string=? body "apos") "'")
          ((and (> len 1) (char=? (string-ref body 0) #\#))
           (let ((hex? (memv (string-ref body 1) '(#\x #\X))))
             (code->string (string->number (substring body (if hex? 2 1) len) (if hex? 16 10)) body)))
          (else (fail "unknown entity" body)))))
    (define (code->string code body)
      (unless (and code (or (<= 1 code #xD7FF) (<= #xE000 code #x10FFFF)))
        (fail "bad character reference" body))
      (string (integer->char code)))

    ;; Skip whitespace, comments and processing instructions between top-level parts.
    (define (skip-misc)
      (skip-ws)
      (cond
        ((accept "<!--") (read-until "-->" "comment") (skip-misc))
        ((accept "<?") (read-until "?>" "processing instruction") (skip-misc))
        ((at? "<!DOCTYPE") (fail "DTD not supported"))
        (else (values))))

    (define (split-qname q)
      (let loop ((k 0))
        (cond
          ((= k (string-length q)) (values #f q))
          ((char=? (string-ref q k) #\:)
           (values (substring q 0 k) (substring q (+ k 1) (string-length q))))
          (else (loop (+ k 1))))))

    (define (resolve prefix env)
      (cond
        ((string=? prefix "xml") xml-ns-uri)
        ((assoc prefix env) => cdr)
        (else (fail "undeclared namespace prefix" prefix))))

    ;; The prefix an xmlns attribute declares, "" for the default namespace, or #f.
    (define (declared-prefix q)
      (cond
        ((string=? q "xmlns") "")
        ((and (> (string-length q) 6) (string=? (substring q 0 6) "xmlns:"))
         (substring q 6 (string-length q)))
        (else #f)))

    (define (read-attr-value)
      (let ((q (peek)))
        (unless (memv q '(#\" #\')) (fail "attribute value must be quoted" i))
        (set! i (+ i 1))
        (let loop ((parts '()) (start i))
          (let ((c (peek)))
            (cond
              ((not c) (fail "unterminated attribute value"))
              ((char=? c q)
               (let ((v (apply string-append (reverse (cons (substring s start i) parts)))))
                 (set! i (+ i 1))
                 v))
              ((char=? c #\<) (fail "'<' in attribute value" i))
              ((char=? c #\&)
               (let ((before (substring s start i)))
                 (set! i (+ i 1))
                 (let ((r (read-reference)))
                   (loop (cons r (cons before parts)) i))))
              (else (set! i (+ i 1)) (loop parts start)))))))

    ;; i is at '<' of a start tag. ENV maps prefixes ("" for the default) to URIs.
    (define (read-element env)
      (expect "<")
      (let ((qname (read-name)))
        (let loop ((raw '()))
          (skip-ws)
          (cond
            ((or (at? "/>") (at? ">"))
             (let* ((raw (reverse raw))
                    (env (fold-left
                          (lambda (env a)
                            (let ((p (declared-prefix (car a))))
                              (cond
                                ((not p) env)
                                ((string=? p "")
                                 (cons (cons "" (if (string=? (cdr a) "") #f (cdr a))) env))
                                (else (cons (cons p (cdr a)) env)))))
                          env raw))
                    (attrs (filter-map-attrs raw env)))
               (let-values (((prefix local) (split-qname qname)))
                 (let ((ns (if prefix (resolve prefix env)
                               (cond ((assoc "" env) => cdr) (else #f)))))
                   (if (accept "/>")
                       (make-xml-element ns local attrs '())
                       (begin (expect ">")
                              (make-xml-element ns local attrs (read-content qname env))))))))
            (else
             (let ((q (read-name)))
               (when (assoc q raw) (fail "duplicate attribute" q))
               (skip-ws)
               (expect "=")
               (skip-ws)
               (loop (cons (cons q (read-attr-value)) raw))))))))

    (define (filter-map-attrs raw env)
      (let loop ((raw raw) (out '()))
        (if (null? raw)
            (reverse out)
            (let ((q (caar raw)) (v (cdar raw)))
              (if (declared-prefix q)
                  (loop (cdr raw) out)
                  (let-values (((prefix local) (split-qname q)))
                    (loop (cdr raw)
                          (cons (make-xml-attribute (and prefix (resolve prefix env)) local v) out))))))))

    ;; Read children up to the end tag of QNAME, merging adjacent text.
    (define (read-content qname env)
      (let loop ((kids '()) (text '()))
        (define (flush)
          (if (null? text) kids (cons (apply string-append (reverse text)) kids)))
        (cond
          ((>= i n) (fail "unclosed element" qname))
          ((accept "</")
           (let ((end (read-name)))
             (unless (string=? end qname) (fail "mismatched end tag" qname end))
             (skip-ws)
             (expect ">")
             (reverse (flush))))
          ((accept "<!--") (read-until "-->" "comment") (loop kids text))
          ((accept "<![CDATA[")
           (let ((t (read-until "]]>" "CDATA section")))
             (loop kids (cons t text))))
          ((accept "<?") (read-until "?>" "processing instruction") (loop kids text))
          ((at? "<!") (fail "unsupported markup declaration" i))
          ((at? "<") (let ((e (read-element env))) (loop (cons e (flush)) '())))
          ((accept "&") (let ((r (read-reference))) (loop kids (cons r text))))
          (else
           (let ((start i))
             (let scan ()
               (when (and (< i n) (not (memv (string-ref s i) '(#\< #\&))))
                 (set! i (+ i 1))
                 (scan)))
             (loop kids (cons (substring s start i) text)))))))

    (accept "\xFEFF;")
    (skip-misc)
    (unless (at? "<") (fail "no root element"))
    (let ((root (read-element '())))
      (skip-misc)
      (when (< i n) (fail "content after the root element" i))
      root)))
