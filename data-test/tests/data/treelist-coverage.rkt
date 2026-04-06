#lang racket/base

;; Coverage-guided model-based property testing for racket/treelist.
;;
;; A single model-based property applies random sequences of treelist
;; operations, checking against a list model at every step.

(require rackcheck
         rackunit
         racket/list
         racket/path
         racket/string
         errortrace/errortrace-lib)

;; ---------------------------------------------------------------------------
;; Treelist operations table — can point to either the normal or
;; instrumented versions.

(struct tl-ops
  (empty length ref set add cons append insert delete rest
   reverse take drop take-right drop-right sublist
   map filter sort member? find for-each
   flatten make ->list ->vector list-> index-of
   chaperone chaperone-state first last empty? ->vector* vector->)
  #:transparent)

;; Load ops from a module (racket/treelist)
(define (load-ops-from mod)
  (define (g name) (dynamic-require mod name))
  (tl-ops (g 'empty-treelist) (g 'treelist-length) (g 'treelist-ref)
          (g 'treelist-set) (g 'treelist-add) (g 'treelist-cons)
          (g 'treelist-append) (g 'treelist-insert) (g 'treelist-delete)
          (g 'treelist-rest) (g 'treelist-reverse)
          (g 'treelist-take) (g 'treelist-drop)
          (g 'treelist-take-right) (g 'treelist-drop-right)
          (g 'treelist-sublist) (g 'treelist-map) (g 'treelist-filter)
          (g 'treelist-sort) (g 'treelist-member?) (g 'treelist-find)
          (g 'treelist-for-each) (g 'treelist-flatten)
          (g 'make-treelist) (g 'treelist->list) (g 'treelist->vector)
          (g 'list->treelist) (g 'treelist-index-of)
          (g 'chaperone-treelist) (g 'treelist-chaperone-state)
          (g 'treelist-first) (g 'treelist-last)
          (g 'treelist-empty?) (g 'treelist->vector) (g 'vector->treelist)))

(define default-ops (load-ops-from 'racket/treelist))

;; Current ops (parameterized for guided vs standard mode)
(define current-ops (make-parameter default-ops))

;; ---------------------------------------------------------------------------
;; Generators

(define gen:element
  (gen:choice
   gen:natural
   (gen:map gen:natural (lambda (n) (- n)))
   gen:boolean
   (gen:one-of '(a b c d e))))

(define (gen:operations max-ops)
  (gen:list (gen:tuple (gen:integer-in 0 33)
                       gen:element
                       gen:natural)
            #:max-length max-ops))

;; ---------------------------------------------------------------------------
;; Model-based test

(define (apply-operations ops)
  (define o (current-ops))
  (define tl-empty (tl-ops-empty o))
  (define tl-length (tl-ops-length o))
  (define tl-set (tl-ops-set o))
  (define tl-add (tl-ops-add o))
  (define tl-cons (tl-ops-cons o))
  (define tl-append (tl-ops-append o))
  (define tl-insert (tl-ops-insert o))
  (define tl-delete (tl-ops-delete o))
  (define tl-rest (tl-ops-rest o))
  (define tl-reverse (tl-ops-reverse o))
  (define tl-take (tl-ops-take o))
  (define tl-drop (tl-ops-drop o))
  (define tl-take-right (tl-ops-take-right o))
  (define tl-drop-right (tl-ops-drop-right o))
  (define tl-sublist (tl-ops-sublist o))
  (define tl-map (tl-ops-map o))
  (define tl-filter (tl-ops-filter o))
  (define tl-sort (tl-ops-sort o))
  (define tl-member? (tl-ops-member? o))
  (define tl-find (tl-ops-find o))
  (define tl-for-each (tl-ops-for-each o))
  (define tl-flatten (tl-ops-flatten o))
  (define tl-make (tl-ops-make o))
  (define tl->list (tl-ops-->list o))
  (define tl-list-> (tl-ops-list-> o))
  (define tl-index-of (tl-ops-index-of o))
  (define tl-chaperone (tl-ops-chaperone o))
  (define tl-chaperone-state (tl-ops-chaperone-state o))
  (define tl-first (tl-ops-first o))
  (define tl-last (tl-ops-last o))
  (define tl-empty? (tl-ops-empty? o))
  (define tl->vector (tl-ops-->vector* o))
  (define tl-vector-> (tl-ops-vector-> o))

  (let loop ([tl tl-empty]
             [model '()]
             [ops ops])
    (cond
      [(null? ops)
       (and (= (tl-length tl) (length model))
            (equal? (tl->list tl) model))]
      [else
       (define op (car ops))
       (if (not (and (list? op) (>= (length op) 3)
                     (integer? (car op)) (integer? (caddr op))))
           (loop tl model (cdr ops))
           (let ()
       (define selector (car op))
       (define elem (cadr op))
       (define raw-idx (caddr op))
       (define len (length model))

       (define-values (new-tl new-model)
         (cond
           [(= selector 0)
            (values (tl-add tl elem) (append model (list elem)))]
           [(= selector 1)
            (values (tl-cons tl elem) (cons elem model))]
           [(and (= selector 2) (> len 0))
            (define idx (modulo raw-idx len))
            (values (tl-set tl idx elem) (list-set model idx elem))]
           [(= selector 3)
            (define idx (modulo raw-idx (add1 len)))
            (values (tl-insert tl idx elem)
                    (append (take model idx) (list elem) (drop model idx)))]
           [(and (= selector 4) (> len 0))
            (define idx (modulo raw-idx len))
            (values (tl-delete tl idx)
                    (append (take model idx) (drop model (add1 idx))))]
           [(= selector 5)
            (values (tl-append tl (tl-list-> (list elem)))
                    (append model (list elem)))]
           [(= selector 6)
            (values (tl-reverse tl) (reverse model))]
           [(and (= selector 7) (> len 0))
            (values (tl-rest tl) (cdr model))]
           [(= selector 8)
            (define n (modulo raw-idx (add1 len)))
            (values (tl-take tl n) (take model n))]
           [(= selector 9)
            (define n (modulo raw-idx (add1 len)))
            (values (tl-drop tl n) (drop model n))]
           [(= selector 10)
            (define n (modulo raw-idx (add1 len)))
            (values (tl-take-right tl n) (take-right model n))]
           [(= selector 11)
            (define n (modulo raw-idx (add1 len)))
            (values (tl-drop-right tl n) (drop-right model n))]
           [(and (= selector 12) (> len 0))
            (define start (modulo raw-idx len))
            (define end* (+ start (modulo raw-idx (- len start -1))))
            (define end** (min end* len))
            (values (tl-sublist tl start end**)
                    (take (drop model start) (- end** start)))]
           [(= selector 13)
            (values (tl-map tl values) model)]
           [(= selector 14)
            (values (tl-filter (lambda (_) #t) tl) model)]
           [(and (= selector 15) (> len 0) (andmap number? model))
            (values (tl-sort tl <) (sort model <))]
           [(= selector 16)
            (define chunk (build-list (add1 (modulo raw-idx 20)) values))
            (values (tl-append tl (tl-list-> chunk))
                    (append model chunk))]
           [(= selector 17)
            (define n (add1 (modulo raw-idx 5)))
            (define new-tl
              (for/fold ([t tl]) ([_ (in-range n)]) (tl-add t elem)))
            (values new-tl (append model (make-list n elem)))]
           [(and (= selector 18) (> len 3))
            (values (tl-filter number? tl) (filter number? model))]
           [(and (= selector 19) (> len 0) (< len 100))
            (values (tl-append tl tl) (append model model))]
           [(and (= selector 20) (> len 0))
            (equal? tl (tl-list-> model))
            (values tl model)]
           [(and (= selector 21) (> len 0))
            (equal-hash-code tl)
            (values tl model)]
           [(and (= selector 22) (> len 0) (< len 20)
                 (andmap (lambda (x) (or (number? x) (boolean? x) (symbol? x))) model))
            (with-handlers ([exn:fail? (lambda (_) (values tl model))])
              (define ser (dynamic-require 'racket/serialize 'serialize))
              (define deser (dynamic-require 'racket/serialize 'deserialize))
              (values (deser (ser tl)) model))]
           [(and (= selector 23) (> len 0))
            (tl-member? tl elem)
            (tl-member? tl (car model))
            (values tl model)]
           [(and (= selector 24) (> len 0))
            (tl-find tl number?)
            (values tl model)]
           [(and (= selector 25) (> len 0))
            (define count 0)
            (tl-for-each tl (lambda (_) (set! count (add1 count))))
            (unless (= count len) (error "for-each count mismatch"))
            (values tl model)]
           [(= selector 26)
            (define inner (tl-list-> (list elem)))
            (define nested (tl-add (tl-add tl-empty inner) elem))
            (tl-flatten nested)
            (values tl model)]
           [(= selector 27)
            (define n (modulo raw-idx 10))
            (tl-make n elem)
            (values tl model)]
           ;; 28: chaperone the treelist (all subsequent ops go through /slow paths)
           [(= selector 28)
            (define my-key (list 'test-key))
            (define ct
              (tl-chaperone tl
                            #:state 'chaperoned
                            #:state-key my-key
                            #:ref (lambda (t pos val state) val)
                            #:set (lambda (t pos val state) (values val state))
                            #:insert (lambda (t pos val state) (values val state))
                            #:prepend (lambda (t other state) (values other state))
                            #:append (lambda (t other state) (values other state))
                            #:delete (lambda (t pos state) state)
                            #:take (lambda (t pos state) state)
                            #:drop (lambda (t pos state) state)))
            ;; Exercise chaperone-state
            (tl-chaperone-state ct my-key)
            ;; Continue with chaperoned treelist — same model
            (values ct model)]
           ;; 29: first/last (exercises those code paths including /slow)
           [(and (= selector 29) (> len 0))
            (tl-first tl)
            (tl-last tl)
            (values tl model)]
           ;; 30: treelist->vector roundtrip
           [(= selector 30)
            (define v (tl->vector tl))
            (define tl2 (tl-vector-> v))
            (values tl2 model)]
           ;; 31: error path — ref out of range (caught)
           [(= selector 31)
            (with-handlers ([exn:fail? void])
              (tl-ops-ref o tl (+ len 10)))
            ;; Also try negative index
            (with-handlers ([exn:fail? void])
              (tl-ops-ref o tl -1))
            ;; Non-integer index
            (with-handlers ([exn:fail? void])
              (tl-ops-ref o tl 'bad))
            (values tl model)]
           ;; 32: error path — delete out of range
           [(= selector 32)
            (with-handlers ([exn:fail? void])
              (tl-delete tl (+ len 10)))
            (with-handlers ([exn:fail? void])
              (tl-take tl (+ len 10)))
            (with-handlers ([exn:fail? void])
              (tl-drop tl (+ len 10)))
            (values tl model)]
           ;; 33: error path — first/last/rest on empty
           [(and (= selector 33) (= len 0))
            (with-handlers ([exn:fail? void]) (tl-first tl))
            (with-handlers ([exn:fail? void]) (tl-last tl))
            (with-handlers ([exn:fail? void]) (tl-rest tl))
            (values tl model)]
           [else (values tl model)]))

       (and (= (tl-length new-tl) (length new-model))
            (equal? (tl->list new-tl) new-model)
            (loop new-tl new-model (cdr ops)))))])))

(define-property prop:model-correspondence
  ([ops (gen:operations 60)])
  (apply-operations ops))

;; ---------------------------------------------------------------------------
;; Standard tests (no instrumentation)

(module+ test
  (check-property (make-config #:tests 500) prop:model-correspondence))

;; ---------------------------------------------------------------------------
;; Coverage-guided tests with instrumented namespace

(module+ guided
  (require rackcheck rackunit racket/list racket/path racket/string
           errortrace/errortrace-lib)

  (define treelist-src
    (simplify-path (collection-file-path "treelist.rkt" "racket")))

  ;; Set up instrumented namespace (same pattern as measure-gvector-coverage)
  (define ns (make-base-namespace))

  (parameterize ([current-namespace ns])
    (define orig (current-load/use-compiled))
    (define target-loaded? #f)
    (current-load/use-compiled
     (lambda (path mod)
       (if (and (path? path) (not target-loaded?)
                (equal? (simplify-path path) treelist-src))
           (begin
             (set! target-loaded? #t)
             (parameterize ([current-load-relative-directory (path-only path)])
               ((current-load) path mod)))
           (orig path mod))))
    (execute-counts-enabled #t)
    (current-compile (make-errortrace-compile-handler))
    (namespace-require 'racket/treelist))

  ;; Load ops from the instrumented namespace
  (define instrumented-ops
    (parameterize ([current-namespace ns])
      (load-ops-from 'racket/treelist)))

  (define (coverage-stats)
    (define counts (get-execute-counts))
    (define tl-counts
      (filter (lambda (c)
                (let ([src (syntax-source (car c))])
                  (and (path? src)
                       (equal? (simplify-path src) treelist-src))))
              counts))
    (define hit (filter (lambda (c) (> (cdr c) 0)) tl-counts))
    (values (length hit) (length tl-counts)))

  ;; Run model-based test with instrumented ops
  (printf "Running coverage-guided model-based test (1000 iterations)...\n")
  (parameterize ([current-ops instrumented-ops])
    (check-property (make-config #:tests 1000) prop:model-correspondence))

  (define-values (h1 t1) (coverage-stats))
  (printf "After 1000 tests: ~a/~a (~a%)\n"
          h1 t1 (real->decimal-string (* 100.0 (/ h1 t1)) 1))

  (parameterize ([current-ops instrumented-ops])
    (check-property (make-config #:tests 2000) prop:model-correspondence))

  (define-values (h2 t2) (coverage-stats))
  (printf "After 3000 tests: ~a/~a (~a%)\n"
          h2 t2 (real->decimal-string (* 100.0 (/ h2 t2)) 1))

  ;; Report uncovered lines
  (define counts (get-execute-counts))
  (define tl-counts
    (filter (lambda (c)
              (let ([src (syntax-source (car c))])
                (and (path? src)
                     (equal? (simplify-path src) treelist-src))))
            counts))
  (define uncov-lines
    (sort (remove-duplicates
           (filter values
                   (for/list ([c tl-counts] #:when (= (cdr c) 0))
                     (syntax-line (car c)))))
          <))
  (printf "\nUncovered lines (~a):\n" (length uncov-lines))
  (define source-lines
    (call-with-input-file treelist-src
      (lambda (in) (for/list ([line (in-lines in)]) line))))
  (for ([line (in-list uncov-lines)])
    (when (<= line (length source-lines))
      (printf "  ~a: ~a\n" line
              (string-trim (list-ref source-lines (sub1 line)))))))
