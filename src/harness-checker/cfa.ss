;; cfa.ss
;; 0CFA control-flow analysis for the harness checker (HC-2).
;;
;; Answers one question per call site: which lambdas can arrive in operator
;; position there? The analysis is flow-insensitive and context-insensitive:
;; every variable has one set of abstract values for the whole program, and
;; the sets grow until nothing changes. termination.ss uses the resulting
;; call-site table to see recursion that reaches a function through a
;; variable, an immediate lambda, a data structure or a built-in HOF.
;;
;; Abstract values:
;;   <integer>      a lambda label (see cfa-lambda records)
;;   (prim . sym)   a free name used as a value: a built-in or a tool
;;   (cell . id)    an allocation site; its contents are one merged set
;;   top            a value the analysis cannot follow
;;
;; Literals and the results of data built-ins are opaque data and have no
;; representation: they are never procedures. A value reaches `top` only by
;; passing through an operator the analysis does not model (a tool, a record
;; constructor or accessor). Calling `top` marks the site unresolved, which
;; termination.ss reports as `unresolved-call` so the checker stays
;; fail-closed.
;;
;; See plans/hc-0cfa.md in the overlord vault for the design.

(library (harness-checker cfa)
  (export cfa-analyze
          cfa-result?
          cfa-result-lambdas
          cfa-result-sites
          cfa-lambda-ref
          cfa-site-of
          cfa-lambda?
          cfa-lambda-label
          cfa-lambda-kind
          cfa-lambda-name
          cfa-lambda-formals
          cfa-lambda-rest
          cfa-lambda-body
          cfa-lambda-parent
          cfa-lambda-expr
          cfa-site?
          cfa-site-expr
          cfa-site-caller
          cfa-site-callees
          cfa-site-callee-labels
          cfa-site-unresolved?
          cfa-hof-callback-position
          cfa-modeled-builtin?)
  (import (rnrs))

  ;; ---------------------------------------------------------------
  ;; Records
  ;; ---------------------------------------------------------------

  ;; One per lambda, case-lambda clause, procedure define, letrec binding
  ;; and named let.
  ;;   kind    - 'define | 'letrec | 'named-let | 'lambda
  ;;   name    - the bound symbol for define/letrec/named-let, else #f
  ;;   formals - list of required formal symbols
  ;;   rest    - rest formal symbol or #f
  ;;   parent  - label of the lexically enclosing lambda, or #f at top level
  ;;   expr    - the source form the label was created for
  (define-record-type cfa-lambda
    (fields label kind name formals rest body parent expr))

  ;; One per application (and per named-let entry or cond `=>` clause).
  ;;   caller   - label of the enclosing lambda, or #f at top level
  ;;   callees  - list of (label . via), via one of
  ;;              'direct | 'hof | 'apply | 'escape | 'named-let | 'cond-arrow
  ;;              | 'opaque (arguments unrelated to the site's own)
  ;;              | (hof . name), name the HOF built-in invoked positionally
  ;;                or #f when it was reached through a spread argument list
  ;;   unresolved? - #t when `top` can reach operator position here
  (define-record-type cfa-site
    (fields expr caller (mutable callees) (mutable unresolved?)))

  (define-record-type cfa-result
    (fields lambdas sites table))

  (define (cfa-lambda-ref result label)
    (find (lambda (l) (= (cfa-lambda-label l) label))
          (cfa-result-lambdas result)))

  (define (cfa-site-of result expr)
    (hashtable-ref (cfa-result-table result) expr #f))

  (define (cfa-site-callee-labels site)
    (let loop ((cs (cfa-site-callees site)) (acc '()))
      (cond
        ((null? cs) (list-sort < acc))
        ((memv (caar cs) acc) (loop (cdr cs) acc))
        (else (loop (cdr cs) (cons (caar cs) acc))))))

  ;; ---------------------------------------------------------------
  ;; Built-in classification
  ;; ---------------------------------------------------------------

  ;; Callback position of each collection HOF, mirroring termination.ss.
  (define hof-callback-positions
    '((map . 0) (for-each . 0) (filter . 0) (remove . 0) (remp . 0)
      (fold-left . 0) (fold-right . 0) (find . 0) (exists . 0)
      (for-all . 0) (memp . 0) (partition . 0)
      (vector-map . 0) (vector-for-each . 0) (string-for-each . 0)))

  (define (cfa-hof-callback-position sym)
    (let ((e (assq sym hof-callback-positions)))
      (and e (cdr e))))

  ;; Built-ins that allocate one structure holding every argument.
  (define allocator-names '(cons list vector make-vector cons*))

  ;; Built-ins that return part of a structure argument. The result is the
  ;; argument's cells plus their contents; returning the cell covers `cdr`
  ;; yielding the rest of a list.
  (define reader-names
    '(car cdr caar cadr cdar cddr caaar caadr cadar caddr
      cdaar cdadr cddar cdddr list-ref list-tail vector-ref
      member memv memq assoc assv assq
      reverse list-copy vector->list list->vector vector-copy))

  ;; Built-ins whose result is opaque data whatever they are given, and
  ;; which never call an argument.
  (define data-builtin-names
    '(+ - * / = < > <= >= zero? positive? negative? odd? even? abs max min
      modulo remainder quotient expt sqrt floor ceiling round truncate
      number? integer? real? exact? inexact? exact->inexact inexact->exact
      number->string string->number not boolean? pair? null? list? length
      symbol? symbol->string string->symbol char? char=? char<? char>?
      char<=? char>=? char-alphabetic? char-numeric? char-whitespace?
      char-upcase char-downcase char->integer integer->char string?
      string-length string-ref string=? string<? string>? string<=?
      string>=? substring string-append string->list list->string
      string-copy string-contains string-upcase string-downcase vector?
      vector-length display newline write format eq? eqv? equal?
      procedure? port? eof-object? void error assert))

  (define control-names
    '(apply values call-with-values dynamic-wind vector-set! vector-fill!
      append))

  (define (cfa-modeled-builtin? sym)
    (and (or (memq sym allocator-names)
             (memq sym reader-names)
             (memq sym data-builtin-names)
             (memq sym control-names)
             (assq sym hof-callback-positions))
         #t))

  (define special-forms
    '(quote quasiquote lambda case-lambda define set! if when unless begin
      and or cond case let let* letrec letrec* let-values let*-values do
      define-record-type parameterize guard))

  ;; ---------------------------------------------------------------
  ;; Sets of abstract values (small lists, equal?-compared)
  ;; ---------------------------------------------------------------

  (define (set-union a b)
    (fold-left (lambda (acc v) (if (member v acc) acc (cons v acc))) a b))

  (define (set-union* sets) (fold-left set-union '() sets))

  (define (cell? v) (and (pair? v) (eq? (car v) 'cell)))
  (define (prim? v) (and (pair? v) (eq? (car v) 'prim)))
  (define (label? v) (integer? v))

  ;; Split formals into (values required rest).
  (define (parse-formals f)
    (let loop ((f f) (req '()))
      (cond
        ((pair? f) (loop (cdr f) (cons (car f) req)))
        ((symbol? f) (values (reverse req) f))
        (else (values (reverse req) #f)))))

  ;; ---------------------------------------------------------------
  ;; The analysis
  ;; ---------------------------------------------------------------

  (define (cfa-analyze exprs)
    (let ((store (make-hashtable equal-hash equal?))
          (lambda-table (make-eq-hashtable))
          (lambdas '())
          (next-label 0)
          (binding-ids (make-eq-hashtable))
          (next-binding 0)
          (site-table (make-eq-hashtable))
          (sites '())
          (changed #f))

      ;; --- store ---
      (define (store-ref key) (hashtable-ref store key '()))
      (define (store-add! key vals)
        (let* ((old (store-ref key))
               (new (set-union old vals)))
          (unless (= (length new) (length old))
            (hashtable-set! store key new)
            (set! changed #t))))

      (define (contents-key cell) (cons 'contents (cdr cell)))
      (define (ret-key label) (cons 'ret label))

      ;; Contents of every cell in a set; `top` reads as `top`.
      (define (contents vals)
        (set-union*
         (map (lambda (v)
                (cond ((cell? v) (store-ref (contents-key v)))
                      ((eq? v 'top) '(top))
                      (else '())))
              vals)))

      ;; --- identities ---
      (define (binding-key obj)
        (or (hashtable-ref binding-ids obj #f)
            (let ((k (cons 'v next-binding)))
              (set! next-binding (+ next-binding 1))
              (hashtable-set! binding-ids obj k)
              k)))

      (define (formal-key label i) (list 'f label i))
      (define (rest-key label) (list 'r label))

      (define (get-lambda! source kind name formals body parent)
        (or (hashtable-ref lambda-table source #f)
            (let-values (((req rest) (parse-formals formals)))
              (let ((l (make-cfa-lambda next-label kind name req rest body
                                        parent source)))
                (set! next-label (+ next-label 1))
                (hashtable-set! lambda-table source l)
                (set! lambdas (cons l lambdas))
                l))))

      (define (lambda-by-label label)
        (find (lambda (l) (= (cfa-lambda-label l) label)) lambdas))

      (define (get-site! expr caller)
        (or (hashtable-ref site-table expr #f)
            (let ((s (make-cfa-site expr caller '() #f)))
              (hashtable-set! site-table expr s)
              (set! sites (cons s sites))
              s)))

      (define (site-add-callee! site label via)
        (let ((entry (cons label via)))
          (unless (member entry (cfa-site-callees site))
            (cfa-site-callees-set! site (cons entry (cfa-site-callees site)))
            (set! changed #t))))

      (define (site-mark-unresolved! site)
        (unless (cfa-site-unresolved? site)
          (cfa-site-unresolved?-set! site #t)
          (set! changed #t)))

      (define (site-cell site) (cons 'cell (cfa-site-expr site)))

      ;; --- environments: alist of (symbol . key) ---
      (define (lookup env sym)
        (let ((e (assq sym env)))
          (if e (store-ref (cdr e)) (list (cons 'prim sym)))))

      (define (bound? env sym) (and (assq sym env) #t))

      ;; --- lambdas ---

      ;; Analyse a lambda's body and return its label. Called every pass;
      ;; the label is stable because it is keyed on the source form.
      (define (eval-lambda-like source kind name formals body env parent)
        (let* ((l (get-lambda! source kind name formals body parent))
               (label (cfa-lambda-label l))
               (env2 (bind-formals l env)))
          (store-add! (ret-key label) (eval-body body env2 label))
          label))

      (define (bind-formals l env)
        (let ((label (cfa-lambda-label l)))
          (let loop ((fs (cfa-lambda-formals l)) (i 0) (env env))
            (if (null? fs)
                (let ((r (cfa-lambda-rest l)))
                  (if r
                      (begin
                        (store-add! (rest-key label)
                                    (list (cons 'cell (rest-key label))))
                        (cons (cons r (rest-key label)) env))
                      env))
                (loop (cdr fs) (+ i 1)
                      (cons (cons (car fs) (formal-key label i)) env))))))

      ;; Flow arguments into a lambda. `spread` (or #f) flows to every
      ;; formal and into the rest list, for apply and HOF callbacks.
      ;; Returns #f when the arity cannot match, else the lambda's result.
      (define (flow-into! label args spread)
        (let* ((l (lambda-by-label label))
               (req (cfa-lambda-formals l))
               (rest (cfa-lambda-rest l))
               (n (length args)))
          (if (and (not spread)
                   (or (< n (length req))
                       (and (not rest) (> n (length req)))))
              #f
              (let loop ((i 0) (as args))
                (cond
                  ((< i (length req))
                   (store-add! (formal-key label i)
                               (set-union (if (pair? as) (car as) '())
                                          (or spread '())))
                   (loop (+ i 1) (if (pair? as) (cdr as) '())))
                  (else
                   (when rest
                     (let ((cell (cons 'cell (rest-key label))))
                       (store-add! (rest-key label) (list cell))
                       (store-add! (contents-key cell)
                                   (set-union (set-union* as)
                                              (or spread '())))))
                   (store-ref (ret-key label))))))))

      ;; Invoke every value in op-set. Returns the union of results.
      (define (invoke! op-set args spread site via)
        (set-union*
         (map (lambda (v)
                (cond
                  ((label? v)
                   (let ((r (flow-into! v args spread)))
                     (if r
                         (begin (site-add-callee! site v via) r)
                         '())))
                  ((prim? v) (apply-builtin! (cdr v) args spread site))
                  ((eq? v 'top)
                   (site-mark-unresolved! site)
                   (escape! (set-union (set-union* args) (or spread '()))
                            site)
                   '(top))
                  (else '())))
              op-set)))

      ;; Values handed to an operator the analysis does not model. Every
      ;; lambda reachable from them may be called with unknown arguments,
      ;; and every reachable cell may be overwritten with unknown values.
      (define (escape! vals site)
        (let loop ((todo vals) (seen '()))
          (unless (null? todo)
            (let ((v (car todo)))
              (cond
                ((member v seen) (loop (cdr todo) seen))
                ((label? v)
                 (flow-into! v '() '(top))
                 (site-add-callee! site v 'escape)
                 (loop (cdr todo) (cons v seen)))
                ((cell? v)
                 (store-add! (contents-key v) '(top))
                 (loop (append (store-ref (contents-key v)) (cdr todo))
                       (cons v seen)))
                (else (loop (cdr todo) (cons v seen))))))))

      ;; --- built-ins ---

      ;; Positional slots a built-in reads, or 0 when it reads only the
      ;; union of its arguments.
      (define (builtin-arity name)
        (cond
          ((memq name '(vector-set! dynamic-wind)) 3)
          ((memq name '(vector-fill! apply call-with-values)) 2)
          ((cfa-hof-callback-position name) => (lambda (pos) (+ pos 2)))
          (else 0)))

      ;; Nesting depth of built-ins invoked with a spread argument list.
      (define spread-depth 0)
      (define spread-depth-limit 8)

      ;; A built-in reached through apply, a HOF callback or
      ;; call-with-values gets its arguments as a spread list, so any
      ;; spread value may sit in any positional slot. Each slot therefore
      ;; holds the spread values as well. Spread built-ins can invoke one
      ;; another without end, as in (apply apply (list apply apply)), so
      ;; past a fixed depth the site fails closed as unresolved.
      (define (apply-builtin! name args spread site)
        (let ((k (builtin-arity name)))
          (cond
            ((or (not (pair? spread)) (= k 0))
             (apply-positional-builtin! name args spread site))
            ((>= spread-depth spread-depth-limit)
             (site-mark-unresolved! site)
             (escape! (set-union (set-union* args) spread) site)
             '(top))
            (else
             (set! spread-depth (+ spread-depth 1))
             (let ((r (apply-positional-builtin!
                        name (widen-args args spread k) spread site)))
               (set! spread-depth (- spread-depth 1))
               r)))))

      (define (widen-args args spread k)
        (let loop ((i 0) (as args) (acc '()))
          (if (and (null? as) (>= i k))
              (reverse acc)
              (loop (+ i 1)
                    (if (pair? as) (cdr as) '())
                    (cons (set-union (if (pair? as) (car as) '()) spread)
                          acc)))))

      (define (apply-positional-builtin! name args spread site)
        (let ((all (set-union (set-union* args) (or spread '()))))
          (cond
            ((memq name allocator-names)
             (let ((cell (site-cell site)))
               (store-add! (contents-key cell) all)
               (list cell)))
            ((memq name reader-names)
             (set-union (filter (lambda (v) (or (cell? v) (eq? v 'top))) all)
                        (contents all)))
            ;; Any argument, spread ones included, can end up as the
            ;; result's tail, which may be improper. The result gets its
            ;; own cell holding every argument and every element, so a
            ;; reader on it yields all of them.
            ((eq? name 'append)
             (let ((cell (site-cell site)))
               (store-add! (contents-key cell) (set-union all (contents all)))
               (set-union (list cell) all)))
            ((memq name data-builtin-names) '())
            ((eq? name 'values) all)
            ((eq? name 'vector-set!)
             (when (= (length args) 3)
               (for-each (lambda (c)
                           (when (cell? c)
                             (store-add! (contents-key c) (caddr args))))
                         (car args)))
             '())
            ((eq? name 'vector-fill!)
             (when (= (length args) 2)
               (for-each (lambda (c)
                           (when (cell? c)
                             (store-add! (contents-key c) (cadr args))))
                         (car args)))
             '())
            ((eq? name 'apply)
             (if (null? args)
                 '()
                 (let* ((f (car args))
                        (more (cdr args))
                        (leading (if (null? more)
                                     '()
                                     (list-head* more (- (length more) 1))))
                        (lst (if (null? more)
                                 '()
                                 (list-ref more (- (length more) 1))))
                        (sp (set-union (contents lst) (or spread '()))))
                   ;; The site's own arguments are apply's only when
                   ;; the site is a positional call headed by apply.
                   ;; An empty spread set is still a spread (round 11, C1).
                   (invoke! f leading sp site
                            (if (and (not spread)
                                     (pair? (cfa-site-expr site))
                                     (eq? (car (cfa-site-expr site)) 'apply))
                                'apply
                                'opaque)))))
            ((eq? name 'call-with-values)
             (if (= (length args) 2)
                 ;; The consumer receives the producer's values, never
                 ;; the site's own arguments.
                 (let ((r (invoke! (car args) '() #f site 'opaque)))
                   (invoke! (cadr args) '() r site 'opaque))
                 '()))
            ((eq? name 'dynamic-wind)
             (if (= (length args) 3)
                 (begin
                   (invoke! (car args) '() #f site 'opaque)
                   (invoke! (caddr args) '() #f site 'opaque)
                   (invoke! (cadr args) '() #f site 'opaque))
                 '()))
            ((cfa-hof-callback-position name)
             => (lambda (pos)
                  (if (> (length args) pos)
                      (let* ((cb (list-ref args pos))
                             (others (remove-index args pos))
                             (elems (set-union (set-union* others)
                                               (contents (set-union* others))))
                             (acc-key (cons 'hof-acc (cfa-site-expr site)))
                             (sp (set-union* (list elems (store-ref acc-key)
                                                   (or spread '()))))
                             ;; The callback's slots match the site's own
                             ;; arguments only when this HOF is invoked
                             ;; positionally; under a spread it is #f.
                             (r (invoke! cb '() sp site
                                         (cons 'hof (and (not (pair? spread))
                                                         name)))))
                        (store-add! acc-key r)
                        (if (memq name '(map vector-map))
                            (let ((cell (site-cell site)))
                              (store-add! (contents-key cell) r)
                              (list cell))
                            (set-union r elems)))
                      '())))
            (else
             ;; Unmodeled operator: a tool, a record constructor or
             ;; accessor. Anything handed to it escapes; it returns `top`
             ;; if it was handed anything that is not opaque data.
             (if (null? all)
                 '()
                 (begin (escape! all site) '(top)))))))

      (define (list-head* l n)
        (if (= n 0) '() (cons (car l) (list-head* (cdr l) (- n 1)))))

      (define (remove-index l i)
        (if (= i 0) (cdr l) (cons (car l) (remove-index (cdr l) (- i 1)))))

      ;; --- bodies and internal defines ---
      (define (flatten-begins exprs)
        (apply append
               (map (lambda (e)
                      (if (and (pair? e) (eq? (car e) 'begin))
                          (flatten-begins (cdr e))
                          (list e)))
                    exprs)))

      (define (define-name e)
        (and (pair? e) (eq? (car e) 'define) (pair? (cdr e))
             (cond ((symbol? (cadr e)) (cadr e))
                   ((and (pair? (cadr e)) (symbol? (caadr e))) (caadr e))
                   (else #f))))

      (define (eval-body exprs env ctx)
        (let* ((flat (flatten-begins exprs))
               (env2 (fold-left
                      (lambda (env e)
                        (let ((n (define-name e)))
                          (if n (cons (cons n (binding-key e)) env) env)))
                      env flat)))
          (let loop ((es flat) (last '()))
            (if (null? es)
                last
                (loop (cdr es) (eval-expr (car es) env2 ctx))))))

      (define (lambda-form? e kw)
        (and (pair? e) (eq? (car e) kw) (pair? (cdr e))))

      ;; Evaluate a binding's right-hand side, naming it when it is a
      ;; lambda or case-lambda.
      (define (eval-named-rhs rhs kind name env ctx)
        (cond
          ((lambda-form? rhs 'lambda)
           (list (eval-lambda-like rhs kind name (cadr rhs) (cddr rhs)
                                   env ctx)))
          ((lambda-form? rhs 'case-lambda)
           (eval-case-lambda rhs kind name env ctx))
          (else (eval-expr rhs env ctx))))

      (define (eval-case-lambda e kind name env ctx)
        (map (lambda (clause)
               (eval-lambda-like clause kind name (car clause) (cdr clause)
                                 env ctx))
             (filter pair? (cdr e))))

      ;; --- expressions ---
      (define (eval-expr e env ctx)
        (cond
          ((symbol? e) (lookup env e))
          ((not (pair? e)) '())
          ((and (symbol? (car e))
                (memq (car e) special-forms)
                (not (bound? env (car e))))
           (eval-special e env ctx))
          (else (eval-application e env ctx))))

      (define (eval-all es env ctx)
        (map (lambda (x) (eval-expr x env ctx)) es))

      (define (eval-application e env ctx)
        (let* ((site (get-site! e ctx))
               (op (eval-expr (car e) env ctx))
               (args (if (list? (cdr e)) (eval-all (cdr e) env ctx) '())))
          (invoke! op args #f site 'direct)))

      (define (eval-quasi q env ctx depth cell)
        (cond
          ((not (pair? q)) '())
          ((and (eq? (car q) 'unquote) (pair? (cdr q)))
           (if (= depth 0)
               (store-add! (contents-key cell) (eval-expr (cadr q) env ctx))
               (eval-quasi (cadr q) env ctx (- depth 1) cell)))
          ((and (eq? (car q) 'unquote-splicing) (pair? (cdr q)))
           (if (= depth 0)
               (let ((v (eval-expr (cadr q) env ctx)))
                 (store-add! (contents-key cell)
                             (set-union v (contents v))))
               (eval-quasi (cadr q) env ctx (- depth 1) cell)))
          ((eq? (car q) 'quasiquote)
           (eval-quasi (cdr q) env ctx (+ depth 1) cell))
          (else
           (eval-quasi (car q) env ctx depth cell)
           (eval-quasi (cdr q) env ctx depth cell))))

      (define (eval-special e env ctx)
        (case (car e)
          ((quote define-record-type) '())
          ((quasiquote)
           (let ((cell (cons 'cell e)))
             (when (pair? (cdr e)) (eval-quasi (cadr e) env ctx 0 cell))
             (list cell)))
          ((lambda)
           (list (eval-lambda-like e 'lambda #f (cadr e) (cddr e) env ctx)))
          ((case-lambda) (eval-case-lambda e 'lambda #f env ctx))
          ((define)
           (let ((n (define-name e)))
             (cond
               ((not n) '())
               ((pair? (cadr e))
                (let ((label (eval-lambda-like e 'define n (cdadr e) (cddr e)
                                               env ctx)))
                  (store-add! (binding-key e) (list label))))
               ((pair? (cddr e))
                (store-add! (binding-key e)
                            (eval-named-rhs (caddr e) 'define n env ctx))))
             '()))
          ((set!)
           (when (and (pair? (cdr e)) (pair? (cddr e)))
             (let ((v (eval-expr (caddr e) env ctx))
                   (b (assq (cadr e) env)))
               (when b (store-add! (cdr b) v))))
           '())
          ((if when unless begin and or)
           (let ((vs (eval-all (cdr e) env ctx)))
             (case (car e)
               ((if) (if (pair? vs) (set-union* (cdr vs)) '()))
               ((and or) (set-union* vs))
               (else (if (pair? vs) (list-ref vs (- (length vs) 1)) '())))))
          ((cond) (eval-cond e env ctx))
          ((case)
           (when (pair? (cdr e)) (eval-expr (cadr e) env ctx))
           (set-union*
            (map (lambda (clause)
                   (if (and (pair? clause) (pair? (cdr clause)))
                       (eval-body (cdr clause) env ctx)
                       '()))
                 (if (pair? (cdr e)) (cddr e) '()))))
          ((let) (eval-let e env ctx))
          ((let*) (eval-let* e env ctx))
          ((letrec letrec*) (eval-letrec e env ctx))
          ((let-values let*-values) (eval-let-values e env ctx))
          ((do) (eval-do e env ctx))
          ((parameterize) (eval-parameterize e env ctx))
          ((guard) (eval-guard e env ctx))
          (else '())))

      ;; (guard (var clause ...) body ...): var holds whatever was raised,
      ;; which can be any value, so it starts as top and a call through it
      ;; is unresolved (HC-2 round 14, I1).
      (define (eval-guard e env ctx)
        (if (and (pair? (cdr e)) (pair? (cadr e)) (symbol? (car (cadr e)))
                 (list? (cdr (cadr e))))
            (let* ((spec (cadr e))
                   (k (binding-key spec))
                   (body-v (eval-body (cddr e) env ctx)))
              (store-add! k '(top))
              (set-union body-v
                         (eval-cond (cons 'cond (cdr spec))
                                    (cons (cons (car spec) k) env) ctx)))
            '()))

      ;; (parameterize ((p v) ...) body ...): Chez calls each p as (p) to
      ;; read the old value and as (p x) to install v, then the old value
      ;; again on exit (HC-2 round 10, I2).
      (define (eval-parameterize e env ctx)
        (if (and (pair? (cdr e)) (list? (cadr e)))
            (let ((site (get-site! e ctx)))
              (for-each
                (lambda (b)
                  (when (and (list? b) (= (length b) 2))
                    (let* ((p (eval-expr (car b) env ctx))
                           (v (eval-expr (cadr b) env ctx))
                           (old (invoke! p '() #f site 'opaque)))
                      (invoke! p (list (set-union v old)) #f site 'opaque))))
                (cadr e))
              (eval-body (cddr e) env ctx))
            '()))

      (define (eval-cond e env ctx)
        (set-union*
         (map (lambda (clause)
                (cond
                  ((not (pair? clause)) '())
                  ((and (pair? (cdr clause)) (eq? (cadr clause) '=>)
                        (pair? (cddr clause)))
                   (let ((t (eval-expr (car clause) env ctx))
                         (f (eval-expr (caddr clause) env ctx))
                         (site (get-site! clause ctx)))
                     (invoke! f (list t) #f site 'cond-arrow)))
                  (else
                   (let ((t (if (eq? (car clause) 'else)
                                '()
                                (eval-expr (car clause) env ctx))))
                     (if (null? (cdr clause)) t (eval-body (cdr clause) env ctx))))))
              (cdr e))))

      (define (binding-pairs bs) (filter (lambda (b) (and (pair? b) (symbol? (car b)))) bs))

      (define (eval-let e env ctx)
        (cond
          ((and (pair? (cdr e)) (symbol? (cadr e)) (pair? (cddr e)))
           ;; named let
           (let* ((name (cadr e))
                  (bs (binding-pairs (caddr e)))
                  (inits (eval-all (map (lambda (b) (if (pair? (cdr b)) (cadr b) #f)) bs)
                                   env ctx))
                  (env-loop (cons (cons name (binding-key e)) env))
                  (label (eval-lambda-like e 'named-let name (map car bs)
                                           (cdddr e) env-loop ctx))
                  (site (get-site! e ctx)))
             (store-add! (binding-key e) (list label))
             (invoke! (list label) inits #f site 'named-let)))
          ((pair? (cdr e))
           (let* ((bs (binding-pairs (cadr e)))
                  (env2 (fold-left
                         (lambda (env2 b)
                           (when (pair? (cdr b))
                             (store-add! (binding-key b)
                                         (eval-expr (cadr b) env ctx)))
                           (cons (cons (car b) (binding-key b)) env2))
                         env bs)))
             (eval-body (cddr e) env2 ctx)))
          (else '())))

      (define (eval-let* e env ctx)
        (if (pair? (cdr e))
            (let ((env2 (fold-left
                         (lambda (env2 b)
                           (when (pair? (cdr b))
                             (store-add! (binding-key b)
                                         (eval-expr (cadr b) env2 ctx)))
                           (cons (cons (car b) (binding-key b)) env2))
                         env (binding-pairs (cadr e)))))
              (eval-body (cddr e) env2 ctx))
            '()))

      (define (eval-letrec e env ctx)
        (if (pair? (cdr e))
            (let* ((bs (binding-pairs (cadr e)))
                   (env2 (fold-left (lambda (env2 b)
                                      (cons (cons (car b) (binding-key b)) env2))
                                    env bs)))
              (for-each (lambda (b)
                          (when (pair? (cdr b))
                            (store-add! (binding-key b)
                                        (eval-named-rhs (cadr b) 'letrec (car b)
                                                        env2 ctx))))
                        bs)
              (eval-body (cddr e) env2 ctx))
            '()))

      ;; Multiple values are merged: `values` returns the union of its
      ;; arguments, so every variable a binding introduces gets the whole
      ;; init set.
      (define (eval-let-values e env ctx)
        (if (pair? (cdr e))
            (let ((env2
                   (fold-left
                    (lambda (env2 b)
                      (if (and (pair? b) (pair? (cdr b)))
                          (let ((v (eval-expr (cadr b)
                                              (if (eq? (car e) 'let*-values) env2 env)
                                              ctx)))
                            (let-values (((req rest) (parse-formals (car b))))
                              (fold-left
                               (lambda (env3 sym)
                                 (let ((k (list 'lv b sym)))
                                   (store-add! k v)
                                   (cons (cons sym k) env3)))
                               env2
                               (if rest (cons rest req) req))))
                          env2))
                    env (cadr e))))
              (eval-body (cddr e) env2 ctx))
            '()))

      (define (eval-do e env ctx)
        (if (and (pair? (cdr e)) (pair? (cddr e)))
            (let* ((specs (binding-pairs (cadr e)))
                   (env2 (fold-left (lambda (env2 s)
                                      (cons (cons (car s) (binding-key s)) env2))
                                    env specs)))
              (for-each (lambda (s)
                          (when (pair? (cdr s))
                            (store-add! (binding-key s) (eval-expr (cadr s) env ctx))
                            (when (pair? (cddr s))
                              (store-add! (binding-key s)
                                          (eval-expr (caddr s) env2 ctx)))))
                        specs)
              (let ((test-clause (caddr e)))
                (eval-body (cdddr e) env2 ctx)
                (if (pair? test-clause)
                    (begin (eval-expr (car test-clause) env2 ctx)
                           (eval-body (cdr test-clause) env2 ctx))
                    '())))
            '()))

      ;; --- fixpoint ---
      (let loop ()
        (set! changed #f)
        (eval-body exprs '() #f)
        (when changed (loop)))

      (make-cfa-result
       (list-sort (lambda (a b) (< (cfa-lambda-label a) (cfa-lambda-label b)))
                  lambdas)
       (reverse sites)
       site-table)))
)
