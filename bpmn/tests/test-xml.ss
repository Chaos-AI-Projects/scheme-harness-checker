;; test-xml.ss
;; Tests for the XML reader the BPMN checker parses charts with (HC-61).
;;
;; Run with: scheme --libdirs ../src --program test-xml.ss

(import (rnrs) (bpmn xml))

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

;; The message of the error xml-read raises, or #f when it returns.
(define (read-error str)
  (guard (e ((message-condition? e) (condition-message e)))
    (xml-read-string str)
    #f))

(define (rejects? str) (and (read-error str) #t))

(define (first-child e)
  (car (filter xml-element? (xml-element-children e))))

(display "Test group: elements and attributes") (newline)

(let ((e (xml-read-string "<?xml version=\"1.0\"?><a x=\"1\" y='two'><b/>hi<c></c></a>")))
  (assert-equal "root name" "a" (xml-element-name e))
  (assert-equal "double-quoted attribute" "1" (xml-attr e "x"))
  (assert-equal "single-quoted attribute" "two" (xml-attr e "y"))
  (assert-equal "missing attribute" #f (xml-attr e "z"))
  (assert-equal "child names in order" '("b" "c")
                (map xml-element-name (filter xml-element? (xml-element-children e))))
  (assert-equal "text between children" "hi" (xml-text e)))

(display "Test group: namespaces") (newline)

(let* ((e (xml-read-string
           "<d:definitions xmlns:d=\"urn:m\" xmlns=\"urn:default\"><task/><o:x xmlns:o=\"urn:o\" o:k=\"v\" k=\"w\"/></d:definitions>"))
       (kids (filter xml-element? (xml-element-children e))))
  (assert-equal "prefixed element namespace" "urn:m" (xml-element-ns e))
  (assert-equal "prefixed element local name" "definitions" (xml-element-name e))
  (assert-equal "default namespace applies to children" "urn:default" (xml-element-ns (car kids)))
  (assert-equal "inner declaration scopes its element" "urn:o" (xml-element-ns (cadr kids)))
  (assert-equal "unprefixed attribute has no namespace" "w" (xml-attr (cadr kids) "k"))
  (assert-equal "prefixed attribute by namespace" "v" (xml-attr-ns (cadr kids) "urn:o" "k"))
  (assert-equal "xmlns declarations are not attributes" '()
                (xml-element-attrs e)))

(assert-equal "undeclared prefix is rejected" #t (rejects? "<p:a/>"))
(assert-equal "declaration does not leak to a sibling" #t
              (rejects? "<a><b xmlns:p=\"urn:p\"/><p:c/></a>"))

(display "Test group: text, entities, CDATA, comments") (newline)

(assert-equal "predefined entities"
              "<>&\"'"
              (xml-text (xml-read-string "<a>&lt;&gt;&amp;&quot;&apos;</a>")))
(assert-equal "character references"
              "AB"
              (xml-text (xml-read-string "<a>&#65;&#x42;</a>")))
(assert-equal "entity in attribute"
              "x < y"
              (xml-attr (xml-read-string "<a c=\"x &lt; y\"/>") "c"))
(assert-equal "CDATA is literal text"
              "a < b && c"
              (xml-text (xml-read-string "<a><![CDATA[a < b && c]]></a>")))
(assert-equal "comments are skipped"
              '("b")
              (map xml-element-name
                   (filter xml-element?
                           (xml-element-children
                            (xml-read-string "<!-- top --><a><!-- <c/> --><b/></a><!-- tail -->")))))
(assert-equal "processing instruction is skipped"
              "b"
              (xml-element-name (first-child (xml-read-string "<a><?pi data?><b/></a>"))))

(display "Test group: rejected input") (newline)

(assert-equal "DTD is rejected" "DTD not supported"
              (read-error "<!DOCTYPE a [<!ENTITY e \"x\">]><a>&e;</a>"))
(assert-equal "unknown entity is rejected" #t (rejects? "<a>&e;</a>"))
(assert-equal "mismatched end tag is rejected" #t (rejects? "<a><b></a></b>"))
(assert-equal "unclosed element is rejected" #t (rejects? "<a><b/>"))
(assert-equal "two roots are rejected" #t (rejects? "<a/><b/>"))
(assert-equal "text outside the root is rejected" #t (rejects? "<a/>junk"))
(assert-equal "duplicate attribute is rejected" #t (rejects? "<a x=\"1\" x=\"2\"/>"))
(assert-equal "unquoted attribute is rejected" #t (rejects? "<a x=1/>"))
(assert-equal "empty input is rejected" #t (rejects? "  "))
(assert-equal "unterminated comment is rejected" #t (rejects? "<a><!-- x</a>"))

(display "Test group: boundaries") (newline)

(assert-equal "empty string has no root" "no root element" (read-error ""))
(assert-equal "empty port has no root" "no root element"
              (guard (e ((message-condition? e) (condition-message e)))
                (xml-read-port (open-string-input-port ""))
                #f))
(assert-equal "a leading byte-order mark is skipped" "a" (xml-element-name (xml-read-string "\xFEFF;<a/>")))
(assert-equal "a byte-order mark alone has no root" "no root element" (read-error "\xFEFF;"))
(assert-equal "DEL is not a name character" "expected a name" (read-error "<a\x7F;/>"))
(assert-equal "every non-ASCII character is a name character" "a\x80;"
              (xml-element-name (xml-read-string "<a\x80;/>")))
(assert-equal "a name may not start with a colon" "undeclared namespace prefix" (read-error "<:a/>"))
(assert-equal "an empty xmlns: prefix is not a declaration" "undeclared namespace prefix"
              (read-error "<a xmlns:=\"urn:x\"/>"))
(assert-equal "an empty comment" "b"
              (xml-element-name (first-child (xml-read-string "<!----><a><!----><b/></a>"))))
(assert-equal "a short processing instruction" "b"
              (xml-element-name (first-child (xml-read-string "<?x?><a><?x?><b/></a>"))))
(assert-equal "text running to the end is an unclosed element" "unclosed element" (read-error "<a>abc"))

(define (char-ref ref) (xml-text (xml-read-string (string-append "<a>" ref "</a>"))))
(assert-equal "one-digit hex reference" "\t" (char-ref "&#x9;"))
(assert-equal "one-digit decimal reference" "\t" (char-ref "&#9;"))
(assert-equal "upper-case X hex reference" "B" (char-ref "&#X42;"))
(assert-equal "lowest allowed code" (string (integer->char 1)) (char-ref "&#1;"))
(assert-equal "last code below the surrogates" (string (integer->char #xD7FF)) (char-ref "&#xD7FF;"))
(assert-equal "first code above the surrogates" (string (integer->char #xE000)) (char-ref "&#xE000;"))
(assert-equal "highest code" (string (integer->char #x10FFFF)) (char-ref "&#x10FFFF;"))
(for-each
 (lambda (ref)
   (assert-equal (string-append ref " is a bad character reference") "bad character reference"
                 (read-error (string-append "<a>" ref "</a>"))))
 '("&#0;" "&#xD800;" "&#xDFFF;" "&#x110000;" "&#xZZ;" "&#x;" "&#a;"))
(assert-equal "a bare # is an unknown entity" "unknown entity" (read-error "<a>&#;</a>"))
(assert-equal "a two-letter name is an unknown entity" "unknown entity" (read-error "<a>&ee;</a>"))
(assert-equal "a reference in an attribute" "B" (xml-attr (xml-read-string "<a c=\"&#x42;\"/>") "c"))

(newline)
(display "Results: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed")
(newline)

(when (> fail-count 0)
  (exit 1))
