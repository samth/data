#lang racket/base

;; Property-based tests for data/gvector.
;;
;; Covers every public API function with both model-based properties
;; (comparing gvector behavior to a reference list) and algebraic
;; properties (relating operations to each other without a model).
;;
;; Includes concurrent property tests that exercise the CAS retry paths
;; in ensure-free-space! and trim!. These compile gvector with
;; GVECTOR_SLEEP=1 so that maybe-sleep calls widen the race window.

(require rackcheck
         rackunit
         data/gvector
         racket/dict
         racket/serialize
         racket/list)

;; ---------------------------------------------------------------------------
;; Generators

(define gen:element
  (gen:choice
   gen:natural
   (gen:map gen:natural (lambda (n) (- n)))
   gen:boolean
   (gen:map (gen:string gen:char-alphanumeric #:max-length 8) values)
   (gen:one-of '(a b c d e))))

(define gen:element-list
  (gen:list gen:element #:max-length 30))

(define gen:nonempty-element-list
  (gen:filter gen:element-list (lambda (l) (not (null? l)))))

(define gen:nat-list
  (gen:list gen:natural #:max-length 30))

;; Raw operation triples for model-based test.
(define (gen:operations max-ops)
  (gen:let ([n (gen:integer-in 1 max-ops)])
    (gen:list (gen:tuple (gen:integer-in 0 7)
                         gen:element
                         gen:natural)
              #:max-length max-ops)))

;; ---------------------------------------------------------------------------
;; Helpers

(define (make-gv lst)
  (list->gvector lst))

;; ---------------------------------------------------------------------------
;; Model-based testing

(define (apply-operations ops)
  (define gv (make-gvector))
  (define model '())
  (for/and ([op (in-list ops)])
    (define selector (car op))
    (define elem (cadr op))
    (define raw-idx (caddr op))
    (define len (length model))
    (cond
      [(= selector 0)
       (gvector-add! gv elem)
       (set! model (append model (list elem)))
       #t]
      [(= selector 1)
       (gvector-add! gv elem elem)
       (set! model (append model (list elem elem)))
       #t]
      [(and (= selector 2) (> len 0))
       (define idx (modulo raw-idx len))
       (gvector-set! gv idx elem)
       (set! model (list-set model idx elem))
       #t]
      [(= selector 3)
       (gvector-set! gv len elem)
       (set! model (append model (list elem)))
       #t]
      [(and (= selector 4) (> len 0))
       (define idx (modulo raw-idx len))
       (gvector-remove! gv idx)
       (set! model (append (take model idx) (drop model (add1 idx))))
       #t]
      [(and (= selector 5) (> len 0))
       (define val (gvector-remove-last! gv))
       (define expected (last model))
       (set! model (drop-right model 1))
       (equal? val expected)]
      [(= selector 6)
       (define idx (modulo raw-idx (add1 len)))
       (gvector-insert! gv idx elem)
       (set! model (append (take model idx) (list elem) (drop model idx)))
       #t]
      [else #t])
    (and (= (gvector-count gv) (length model))
         (equal? (gvector->list gv) model))))

(define-property prop:model-correspondence
  ([ops (gen:operations 40)])
  (apply-operations ops))

;; =========================================================================
;; Per-function properties
;; =========================================================================

;; --- gvector? ---

(define-property prop:gvector?-positive
  ([lst gen:element-list])
  (gvector? (make-gv lst)))

(define-property prop:gvector?-negative
  ([lst gen:element-list])
  (and (not (gvector? lst))
       (not (gvector? (list->vector lst)))
       (not (gvector? 42))))

;; --- make-gvector ---

(define-property prop:make-gvector-empty
  ([cap (gen:integer-in 0 100)])
  (let ([gv (make-gvector #:capacity cap)])
    (and (gvector? gv)
         (= (gvector-count gv) 0))))

;; --- gvector (constructor) ---

(define-property prop:constructor-matches-list
  ([lst gen:element-list])
  (equal? (gvector->list (apply gvector lst)) lst))

(define-property prop:constructor-count
  ([lst gen:element-list])
  (= (gvector-count (apply gvector lst)) (length lst)))

;; --- gvector-count ---

(define-property prop:count-consistent
  ([lst gen:element-list])
  (= (gvector-count (make-gv lst)) (length lst)))

(define-property prop:count-zero-when-empty
  ([cap (gen:integer-in 0 50)])
  (= (gvector-count (make-gvector #:capacity cap)) 0))

(define-property prop:count-increments-on-add
  ([lst gen:element-list]
   [elem gen:element])
  (let ([gv (make-gv lst)])
    (gvector-add! gv elem)
    (= (gvector-count gv) (add1 (length lst)))))

(define-property prop:count-decrements-on-remove
  ([lst gen:nonempty-element-list])
  (let ([gv (make-gv lst)])
    (gvector-remove-last! gv)
    (= (gvector-count gv) (sub1 (length lst)))))

;; --- gvector-ref ---

(define-property prop:ref-matches-list-ref
  ([lst gen:nonempty-element-list])
  (let ([gv (make-gv lst)])
    (for/and ([i (in-range (length lst))])
      (equal? (gvector-ref gv i) (list-ref lst i)))))

(define-property prop:ref-default-value
  ([lst gen:element-list]
   [extra (gen:integer-in 0 10)])
  (eq? (gvector-ref (make-gv lst) (+ (length lst) extra) 'missing)
       'missing))

(define-property prop:ref-default-thunk
  ([lst gen:element-list]
   [extra (gen:integer-in 0 10)])
  (eq? (gvector-ref (make-gv lst) (+ (length lst) extra) (lambda () 'called))
       'called))

(define-property prop:ref-out-of-range-errors
  ([lst gen:element-list]
   [extra (gen:integer-in 1 10)])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (gvector-ref (make-gv lst) (+ (length lst) extra))
    #f))

;; --- gvector-set! ---

(define-property prop:set-ref-roundtrip
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))])
    (gvector-set! gv pos elem)
    (equal? (gvector-ref gv pos) elem)))

(define-property prop:set-doesnt-change-count
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))])
    (gvector-set! gv pos elem)
    (= (gvector-count gv) (length lst))))

(define-property prop:set-doesnt-change-other-elements
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))])
    (gvector-set! gv pos elem)
    (for/and ([i (in-range (length lst))]
              #:unless (= i pos))
      (equal? (gvector-ref gv i) (list-ref lst i)))))

(define-property prop:set-at-end-acts-as-add
  ([lst gen:element-list]
   [elem gen:element])
  (let ([gv (make-gv lst)])
    (gvector-set! gv (length lst) elem)
    (and (= (gvector-count gv) (add1 (length lst)))
         (equal? (gvector-ref gv (length lst)) elem))))

(define-property prop:last-set-wins
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [vals (gen:list gen:element #:max-length 10)])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))])
    (for ([v (in-list vals)])
      (gvector-set! gv pos v))
    (or (null? vals)
        (equal? (gvector-ref gv pos) (last vals)))))

;; --- gvector-add! ---

(define-property prop:add-appends
  ([lst gen:element-list]
   [elem gen:element])
  (let ([gv (make-gv lst)])
    (gvector-add! gv elem)
    (equal? (gvector->list gv) (append lst (list elem)))))

(define-property prop:add-multi-appends
  ([lst gen:element-list]
   [a gen:element]
   [b gen:element]
   [c gen:element])
  (let ([gv (make-gv lst)])
    (gvector-add! gv a b c)
    (equal? (gvector->list gv) (append lst (list a b c)))))

(define-property prop:add-increases-count-by-n
  ([lst gen:element-list]
   [extras gen:nonempty-element-list])
  (let ([gv (make-gv lst)])
    (apply gvector-add! gv extras)
    (= (gvector-count gv) (+ (length lst) (length extras)))))

;; --- gvector-insert! ---

(define-property prop:insert-preserves-others
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (gvector-insert! gv pos elem)
    (equal? (gvector->list gv)
            (append (take lst pos) (list elem) (drop lst pos)))))

(define-property prop:insert-increases-count
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (gvector-insert! gv pos elem)
    (= (gvector-count gv) (add1 (length lst)))))

(define-property prop:insert-at-0-prepends
  ([lst gen:element-list]
   [elem gen:element])
  (let ([gv (make-gv lst)])
    (gvector-insert! gv 0 elem)
    (and (equal? (gvector-ref gv 0) elem)
         (equal? (gvector->list gv) (cons elem lst)))))

(define-property prop:insert-at-end-appends
  ([lst gen:element-list]
   [elem gen:element])
  (let ([gv (make-gv lst)])
    (gvector-insert! gv (length lst) elem)
    (equal? (gvector->list gv) (append lst (list elem)))))

;; --- gvector-remove! ---

(define-property prop:remove-preserves-others
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))])
    (gvector-remove! gv pos)
    (equal? (gvector->list gv)
            (append (take lst pos) (drop lst (add1 pos))))))

(define-property prop:remove-decreases-count
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))])
    (gvector-remove! gv pos)
    (= (gvector-count gv) (sub1 (length lst)))))

;; --- gvector-remove-last! ---

(define-property prop:remove-last-returns-last
  ([lst gen:nonempty-element-list])
  (equal? (gvector-remove-last! (make-gv lst))
          (last lst)))

(define-property prop:remove-last-leaves-init
  ([lst gen:nonempty-element-list])
  (let ([gv (make-gv lst)])
    (gvector-remove-last! gv)
    (equal? (gvector->list gv) (drop-right lst 1))))

(define-property prop:remove-last-errors-on-empty
  ([cap (gen:integer-in 0 20)])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (gvector-remove-last! (make-gvector #:capacity cap))
    #f))

;; --- Inverse pairs ---

(define-property prop:add-remove-last-identity
  ([lst gen:element-list]
   [elem gen:element])
  (let ([gv (make-gv lst)])
    (gvector-add! gv elem)
    (gvector-remove-last! gv)
    (equal? (gvector->list gv) lst)))

(define-property prop:insert-remove-identity
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (gvector-insert! gv pos elem)
    (gvector-remove! gv pos)
    (equal? (gvector->list gv) lst)))

;; --- gvector-append! ---

(define-property prop:append!-correct
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([gv1 (make-gv lst1)]
        [gv2 (make-gv lst2)])
    (gvector-append! gv1 gv2)
    (equal? (gvector->list gv1) (append lst1 lst2))))

(define-property prop:append!-count-is-sum
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([gv1 (make-gv lst1)]
        [gv2 (make-gv lst2)])
    (gvector-append! gv1 gv2)
    (= (gvector-count gv1) (+ (length lst1) (length lst2)))))

(define-property prop:append!-doesnt-modify-source
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([gv1 (make-gv lst1)]
        [gv2 (make-gv lst2)])
    (gvector-append! gv1 gv2)
    (equal? (gvector->list gv2) lst2)))

(define-property prop:append!-empty-is-identity
  ([lst gen:element-list])
  (let ([gv (make-gv lst)]
        [empty (make-gvector)])
    (gvector-append! gv empty)
    (equal? (gvector->list gv) lst)))

;; --- gvector-append (non-mutating, currently buggy) ---

;; gvector-append should return a new gvector with combined contents
;; and not modify either argument.
;; NOTE: This property currently FAILS due to a bug in gvector-append:
;; it returns void (vector-copy! return value) and uses wrong copy offset.
(define-property prop:append-returns-gvector
  ([lst1 gen:nat-list]
   [lst2 gen:nat-list])
  (gvector? (gvector-append (make-gv lst1) (make-gv lst2))))

(define-property prop:append-correct
  ([lst1 gen:nat-list]
   [lst2 gen:nat-list])
  (equal? (gvector->list (gvector-append (make-gv lst1) (make-gv lst2)))
          (append lst1 lst2)))

(define-property prop:append-count-is-sum
  ([lst1 gen:nat-list]
   [lst2 gen:nat-list])
  (= (gvector-count (gvector-append (make-gv lst1) (make-gv lst2)))
     (+ (length lst1) (length lst2))))

(define-property prop:append-doesnt-modify-args
  ([lst1 gen:nat-list]
   [lst2 gen:nat-list])
  (let ([gv1 (make-gv lst1)]
        [gv2 (make-gv lst2)])
    (gvector-append gv1 gv2)
    (and (equal? (gvector->list gv1) lst1)
         (equal? (gvector->list gv2) lst2))))

;; --- Roundtrips: gvector->list, gvector->vector, list->gvector, vector->gvector ---

(define-property prop:list-roundtrip
  ([lst gen:element-list])
  (equal? (gvector->list (list->gvector lst)) lst))

(define-property prop:vector-roundtrip
  ([lst gen:element-list])
  (let ([v (list->vector lst)])
    (equal? (gvector->vector (vector->gvector v)) v)))

(define-property prop:gvector->vector-length
  ([lst gen:element-list])
  (= (vector-length (gvector->vector (make-gv lst))) (length lst)))

(define-property prop:gvector->list-length
  ([lst gen:element-list])
  (= (length (gvector->list (make-gv lst))) (length lst)))

;; --- Equality and hashing ---

(define-property prop:equal-same-contents
  ([lst gen:element-list])
  (equal? (make-gv lst) (make-gv lst)))

(define-property prop:equal-independent-of-capacity
  ([lst gen:element-list]
   [cap1 (gen:integer-in 0 50)]
   [cap2 (gen:integer-in 0 50)])
  (let ([gv1 (make-gvector #:capacity cap1)]
        [gv2 (make-gvector #:capacity cap2)])
    (for ([x (in-list lst)])
      (gvector-add! gv1 x)
      (gvector-add! gv2 x))
    (equal? gv1 gv2)))

(define-property prop:not-equal-different-length
  ([lst gen:nonempty-element-list]
   [elem gen:element])
  (not (equal? (make-gv lst) (make-gv (cons elem lst)))))

(define-property prop:not-equal-different-contents
  ([lst gen:nonempty-element-list]
   [elem gen:element])
  (let ([gv1 (make-gv lst)]
        [gv2 (make-gv lst)])
    (gvector-set! gv2 0 (list 'unique-sentinel elem))
    (not (equal? gv1 gv2))))

(define-property prop:hash-consistent-with-equal
  ([lst gen:element-list])
  (= (equal-hash-code (make-gv lst))
     (equal-hash-code (make-gv lst))))

(define-property prop:hash-independent-of-capacity
  ([lst gen:element-list]
   [cap1 (gen:integer-in 0 50)]
   [cap2 (gen:integer-in 0 50)])
  (let ([gv1 (make-gvector #:capacity cap1)]
        [gv2 (make-gvector #:capacity cap2)])
    (for ([x (in-list lst)])
      (gvector-add! gv1 x)
      (gvector-add! gv2 x))
    (= (equal-hash-code gv1) (equal-hash-code gv2))))

;; --- Iteration: in-gvector ---

(define-property prop:in-gvector-matches-list
  ([lst gen:element-list])
  (equal? (for/list ([x (in-gvector (make-gv lst))]) x) lst))

(define-property prop:in-gvector-count
  ([lst gen:element-list])
  (= (for/sum ([_ (in-gvector (make-gv lst))]) 1) (length lst)))

;; sequence protocol (using gvector directly in for)
(define-property prop:sequence-matches-list
  ([lst gen:element-list])
  (equal? (for/list ([x (make-gv lst)]) x) lst))

;; --- for/gvector ---

(define-property prop:for-gvector-correct
  ([lst gen:element-list])
  (equal? (gvector->list (for/gvector ([x (in-list lst)]) x)) lst))

(define-property prop:for-gvector-with-filter
  ([lst gen:nat-list])
  (equal? (gvector->list (for/gvector ([x (in-list lst)]
                                        #:when (even? x))
                           x))
          (filter even? lst)))

;; --- for*/gvector ---

(define-property prop:for*/gvector-correct
  ([n (gen:integer-in 0 6)]
   [m (gen:integer-in 0 6)])
  (equal? (gvector->list (for*/gvector ([i (in-range n)]
                                         [j (in-range m)])
                           (+ (* i m) j)))
          (for*/list ([i (in-range n)]
                      [j (in-range m)])
            (+ (* i m) j))))

;; --- Serialization ---

(define-property prop:serialize-roundtrip
  ([lst (gen:list gen:natural #:max-length 20)])
  (equal? (gvector->list (deserialize (serialize (make-gv lst)))) lst))

(define-property prop:serialize-preserves-count
  ([lst (gen:list gen:natural #:max-length 20)])
  (= (gvector-count (deserialize (serialize (make-gv lst)))) (length lst)))

;; --- Dict protocol ---

(define-property prop:dict-ref-correct
  ([lst gen:nonempty-element-list])
  (let ([gv (make-gv lst)])
    (for/and ([i (in-range (length lst))])
      (equal? (dict-ref gv i) (list-ref lst i)))))

(define-property prop:dict-ref-default
  ([lst gen:element-list]
   [extra (gen:integer-in 0 5)])
  (eq? (dict-ref (make-gv lst) (+ (length lst) extra) 'nope)
       'nope))

(define-property prop:dict-set!-works
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))])
    (dict-set! gv pos elem)
    (equal? (dict-ref gv pos) elem)))

(define-property prop:dict-remove!-works
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))]
         [old-count (gvector-count gv)])
    (dict-remove! gv pos)
    (= (gvector-count gv) (sub1 old-count))))

(define-property prop:dict-count-matches
  ([lst gen:element-list])
  (= (dict-count (make-gv lst)) (length lst)))

(define-property prop:dict-map-correct
  ([lst gen:element-list])
  (equal? (dict-map (make-gv lst) list)
          (for/list ([i (in-naturals)] [v (in-list lst)])
            (list i v))))

(define-property prop:dict-keys-are-indices
  ([lst gen:element-list])
  (equal? (dict-keys (make-gv lst))
          (for/list ([i (in-range (length lst))]) i)))

;; --- Capacity and resizing ---

(define-property prop:grow-past-capacity
  ([cap (gen:integer-in 1 5)]
   [lst (gen:list gen:natural #:max-length 50)])
  (let ([gv (make-gvector #:capacity cap)])
    (for ([x (in-list lst)]) (gvector-add! gv x))
    (equal? (gvector->list gv) lst)))

(define-property prop:heavy-shrink
  ([n (gen:integer-in 10 50)]
   [keep (gen:integer-in 0 5)])
  (let ([gv (make-gvector)])
    (for ([i (in-range n)]) (gvector-add! gv i))
    (define actual-keep (min keep n))
    (for ([_ (in-range (- n actual-keep))]) (gvector-remove-last! gv))
    (and (= (gvector-count gv) actual-keep)
         (equal? (gvector->list gv)
                 (for/list ([i (in-range actual-keep)]) i)))))

(define-property prop:add-remove-all-empty
  ([lst gen:element-list])
  (let ([gv (make-gvector)])
    (for ([x (in-list lst)]) (gvector-add! gv x))
    (for ([_ (in-range (length lst))]) (gvector-remove-last! gv))
    (and (= (gvector-count gv) 0)
         (equal? (gvector->list gv) '()))))

(define-property prop:alternating-add-remove
  ([adds (gen:list gen:element #:max-length 20)]
   [removes (gen:list gen:boolean #:max-length 20)])
  (let ([gv (make-gvector)]
        [model '()])
    (for ([a (in-list adds)]
          [should-remove? (in-list removes)])
      (gvector-add! gv a)
      (set! model (append model (list a)))
      (when (and should-remove? (> (length model) 0))
        (gvector-remove-last! gv)
        (set! model (drop-right model 1))))
    (equal? (gvector->list gv) model)))

;; --- Algebraic properties (non-model-based) ---

;; Appending then counting = sum of counts
(define-property prop:append!-count-additive
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([gv1 (make-gv lst1)]
        [gv2 (make-gv lst2)]
        [n1 (length lst1)]
        [n2 (length lst2)])
    (gvector-append! gv1 gv2)
    (= (gvector-count gv1) (+ n1 n2))))

;; insert then count = old count + 1
(define-property prop:insert-count-plus-one
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (add1 (length lst)))]
         [n (gvector-count gv)])
    (gvector-insert! gv pos elem)
    (= (gvector-count gv) (add1 n))))

;; remove then count = old count - 1
(define-property prop:remove-count-minus-one
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([gv (make-gv lst)]
         [pos (modulo pos-raw (length lst))]
         [n (gvector-count gv)])
    (gvector-remove! gv pos)
    (= (gvector-count gv) (sub1 n))))

;; gvector->vector then vector-length = count
(define-property prop:to-vector-length-is-count
  ([lst gen:element-list])
  (let ([gv (make-gv lst)])
    (= (vector-length (gvector->vector gv)) (gvector-count gv))))

;; gvector->list then length = count
(define-property prop:to-list-length-is-count
  ([lst gen:element-list])
  (let ([gv (make-gv lst)])
    (= (length (gvector->list gv)) (gvector-count gv))))

;; set! is idempotent: setting same value twice = setting once
(define-property prop:set-idempotent
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([gv1 (make-gv lst)]
         [gv2 (make-gv lst)]
         [pos (modulo pos-raw (length lst))])
    (gvector-set! gv1 pos elem)
    (gvector-set! gv2 pos elem)
    (gvector-set! gv2 pos elem)
    (equal? gv1 gv2)))

;; add! is like insert at end
(define-property prop:add-is-insert-at-end
  ([lst gen:element-list]
   [elem gen:element])
  (let ([gv1 (make-gv lst)]
        [gv2 (make-gv lst)])
    (gvector-add! gv1 elem)
    (gvector-insert! gv2 (length lst) elem)
    (equal? gv1 gv2)))

;; remove at end = remove-last
(define-property prop:remove-end-is-remove-last
  ([lst gen:nonempty-element-list])
  (let ([gv1 (make-gv lst)]
        [gv2 (make-gv lst)])
    (gvector-remove! gv1 (sub1 (length lst)))
    (gvector-remove-last! gv2)
    (equal? gv1 gv2)))

;; Serialization preserves equality
(define-property prop:serialize-preserves-equality
  ([lst (gen:list gen:natural #:max-length 20)])
  (equal? (make-gv lst) (deserialize (serialize (make-gv lst)))))

;; Commutative: order of set! on different indices doesn't matter
(define-property prop:set-different-indices-commute
  ([lst gen:nonempty-element-list]
   [pos1-raw gen:natural]
   [pos2-raw gen:natural]
   [e1 gen:element]
   [e2 gen:element])
  (let ([len (length lst)])
    (if (< len 2)
        #t
        (let ([pos1 (modulo pos1-raw len)]
              [pos2 (modulo pos2-raw len)])
          (if (= pos1 pos2)
              #t
              (let ([gv1 (make-gv lst)]
                    [gv2 (make-gv lst)])
                (gvector-set! gv1 pos1 e1)
                (gvector-set! gv1 pos2 e2)
                (gvector-set! gv2 pos2 e2)
                (gvector-set! gv2 pos1 e1)
                (equal? gv1 gv2)))))))

;; Append! is associative in effect: (a ++ b) ++ c = a ++ (b ++ c)
;; (comparing final contents)
(define-property prop:append!-associative
  ([l1 gen:nat-list]
   [l2 gen:nat-list]
   [l3 gen:nat-list])
  (let ([gv-left (make-gv l1)]
        [gv-right (make-gv l1)])
    ;; left: (gv1 ++ gv2) ++ gv3
    (gvector-append! gv-left (make-gv l2))
    (gvector-append! gv-left (make-gv l3))
    ;; right: gv1 ++ (gv2 ++ gv3)
    (let ([gv23 (make-gv l2)])
      (gvector-append! gv23 (make-gv l3))
      (gvector-append! gv-right gv23))
    (equal? gv-left gv-right)))

;; Append! with empty right = no change
(define-property prop:append!-right-identity
  ([lst gen:element-list])
  (let ([gv (make-gv lst)])
    (gvector-append! gv (make-gvector))
    (equal? (gvector->list gv) lst)))

;; Append! with empty left = copy of right
(define-property prop:append!-left-identity
  ([lst gen:element-list])
  (let ([gv (make-gvector)])
    (gvector-append! gv (make-gv lst))
    (equal? (gvector->list gv) lst)))

;; for/gvector count = source count (no filter)
(define-property prop:for-gvector-count
  ([lst gen:element-list])
  (= (gvector-count (for/gvector ([x (in-list lst)]) x)) (length lst)))

;; for*/gvector count = product of ranges
(define-property prop:for*/gvector-count
  ([n (gen:integer-in 0 6)]
   [m (gen:integer-in 0 6)])
  (= (gvector-count (for*/gvector ([i (in-range n)] [j (in-range m)]) (cons i j)))
     (* n m)))

;; Reversing a gvector twice = original
(define-property prop:double-reverse-identity
  ([lst gen:element-list])
  (let* ([gv (make-gv lst)]
         [reversed (make-gv (reverse (gvector->list gv)))]
         [double-reversed (make-gv (reverse (gvector->list reversed)))])
    (equal? gv double-reversed)))

;; --- Error path properties ---

;; Bad type for gvector operations raises an error
(define-property prop:ref-rejects-non-gvector
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (gvector-ref x 0)
    #f))

(define-property prop:set-rejects-non-gvector
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (gvector-set! x 0 'v)
    #f))

(define-property prop:add-rejects-non-gvector
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (gvector-add! x 1)
    #f))

(define-property prop:count-rejects-non-gvector
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (gvector-count x)
    #f))

(define-property prop:ref-rejects-non-integer-index
  ([lst gen:nonempty-element-list])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (gvector-ref (make-gv lst) 'not-an-integer)
    #f))

(define-property prop:vector->gvector-rejects-non-vector
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (vector->gvector x)
    #f))

(define-property prop:list->gvector-rejects-non-list
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (list->gvector x)
    #f))

(define-property prop:make-gvector-rejects-negative-capacity
  ([n (gen:integer-in 1 100)])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (make-gvector #:capacity (- n))
    #f))

;; --- for/gvector multi-value path ---

(define-property prop:for-gvector-multi-value
  ([lst gen:nat-list])
  (let ([gv (for/gvector ([x (in-list lst)]) (values x (add1 x)))])
    ;; Each iteration produces two values, both get added
    (= (gvector-count gv) (* 2 (length lst)))))

;; --- Heavy resize: many adds from tiny capacity ---

(define-property prop:resize-stress
  ([n (gen:integer-in 50 200)])
  (let ([gv (make-gvector #:capacity 1)])
    (for ([i (in-range n)]) (gvector-add! gv i))
    (and (= (gvector-count gv) n)
         (for/and ([i (in-range n)])
           (= (gvector-ref gv i) i)))))

;; --- Shrink stress: add many then remove down to near-zero ---

(define-property prop:shrink-stress
  ([n (gen:integer-in 50 200)])
  (let ([gv (make-gvector)])
    (for ([i (in-range n)]) (gvector-add! gv i))
    ;; Remove all but 1
    (for ([_ (in-range (sub1 n))]) (gvector-remove-last! gv))
    (and (= (gvector-count gv) 1)
         (= (gvector-ref gv 0) 0))))

;; ---------------------------------------------------------------------------
;; Run all properties

(module+ test
  ;; Type predicates
  (check-property prop:gvector?-positive)
  (check-property prop:gvector?-negative)

  ;; Constructors
  (check-property prop:make-gvector-empty)
  (check-property prop:constructor-matches-list)
  (check-property prop:constructor-count)

  ;; Count
  (check-property prop:count-consistent)
  (check-property prop:count-zero-when-empty)
  (check-property prop:count-increments-on-add)
  (check-property prop:count-decrements-on-remove)

  ;; Ref
  (check-property prop:ref-matches-list-ref)
  (check-property prop:ref-default-value)
  (check-property prop:ref-default-thunk)
  (check-property prop:ref-out-of-range-errors)

  ;; Set
  (check-property prop:set-ref-roundtrip)
  (check-property prop:set-doesnt-change-count)
  (check-property prop:set-doesnt-change-other-elements)
  (check-property prop:set-at-end-acts-as-add)
  (check-property prop:last-set-wins)

  ;; Add
  (check-property prop:add-appends)
  (check-property prop:add-multi-appends)
  (check-property prop:add-increases-count-by-n)

  ;; Insert
  (check-property prop:insert-preserves-others)
  (check-property prop:insert-increases-count)
  (check-property prop:insert-at-0-prepends)
  (check-property prop:insert-at-end-appends)

  ;; Remove
  (check-property prop:remove-preserves-others)
  (check-property prop:remove-decreases-count)

  ;; Remove-last
  (check-property prop:remove-last-returns-last)
  (check-property prop:remove-last-leaves-init)
  (check-property prop:remove-last-errors-on-empty)

  ;; Inverse pairs
  (check-property prop:add-remove-last-identity)
  (check-property prop:insert-remove-identity)

  ;; Append!
  (check-property prop:append!-correct)
  (check-property prop:append!-count-is-sum)
  (check-property prop:append!-doesnt-modify-source)
  (check-property prop:append!-empty-is-identity)

  ;; Append (non-mutating) — expected to FAIL due to gvector-append bug
  ;; Uncomment to demonstrate:
  ;; (check-property prop:append-returns-gvector)
  ;; (check-property prop:append-correct)
  ;; (check-property prop:append-count-is-sum)
  ;; (check-property prop:append-doesnt-modify-args)

  ;; Roundtrips
  (check-property prop:list-roundtrip)
  (check-property prop:vector-roundtrip)
  (check-property prop:gvector->vector-length)
  (check-property prop:gvector->list-length)

  ;; Equality and hashing
  (check-property prop:equal-same-contents)
  (check-property prop:equal-independent-of-capacity)
  (check-property prop:not-equal-different-length)
  (check-property prop:not-equal-different-contents)
  (check-property prop:hash-consistent-with-equal)
  (check-property prop:hash-independent-of-capacity)

  ;; Iteration
  (check-property prop:in-gvector-matches-list)
  (check-property prop:in-gvector-count)
  (check-property prop:sequence-matches-list)

  ;; for/gvector, for*/gvector
  (check-property prop:for-gvector-correct)
  (check-property prop:for-gvector-with-filter)
  ;; prop:for*/gvector-correct fails: for*/gvector drops elements
  ;; from inner iterations. Shrunk counterexample: n=1, m=2.
  ;; (check-property prop:for*/gvector-correct)

  ;; Serialization
  (check-property prop:serialize-roundtrip)
  (check-property prop:serialize-preserves-count)

  ;; Dict protocol
  (check-property prop:dict-ref-correct)
  (check-property prop:dict-ref-default)
  (check-property prop:dict-set!-works)
  (check-property prop:dict-remove!-works)
  (check-property prop:dict-count-matches)
  (check-property prop:dict-map-correct)
  (check-property prop:dict-keys-are-indices)

  ;; Capacity and resizing
  (check-property prop:grow-past-capacity)
  (check-property prop:heavy-shrink)
  (check-property prop:add-remove-all-empty)
  (check-property prop:alternating-add-remove)

  ;; Algebraic properties
  (check-property prop:append!-count-additive)
  (check-property prop:insert-count-plus-one)
  (check-property prop:remove-count-minus-one)
  (check-property prop:to-vector-length-is-count)
  (check-property prop:to-list-length-is-count)
  (check-property prop:set-idempotent)
  (check-property prop:add-is-insert-at-end)
  (check-property prop:remove-end-is-remove-last)
  (check-property prop:serialize-preserves-equality)
  (check-property prop:set-different-indices-commute)
  (check-property prop:append!-associative)
  (check-property prop:append!-right-identity)
  (check-property prop:append!-left-identity)
  (check-property prop:for-gvector-count)
  ;; prop:for*/gvector-count fails due to same for*/gvector bug.
  ;; (check-property prop:for*/gvector-count)
  (check-property prop:double-reverse-identity)

  ;; Error paths
  (check-property prop:ref-rejects-non-gvector)
  (check-property prop:set-rejects-non-gvector)
  (check-property prop:add-rejects-non-gvector)
  (check-property prop:count-rejects-non-gvector)
  (check-property prop:ref-rejects-non-integer-index)
  (check-property prop:vector->gvector-rejects-non-vector)
  (check-property prop:list->gvector-rejects-non-list)
  (check-property prop:make-gvector-rejects-negative-capacity)

  ;; for/gvector multi-value
  (check-property prop:for-gvector-multi-value)

  ;; Resize/shrink stress
  (check-property prop:resize-stress)
  (check-property prop:shrink-stress)

  ;; Model-based with more iterations
  (check-property (make-config #:tests 200) prop:model-correspondence)

  ;; -------------------------------------------------------------------
  ;; Concrete regression tests for known bugs found by the properties
  ;; above. These are the shrunk counterexamples.

  ;; Bug: gvector-append returns void (vector-copy! return value)
  ;; and copies from wrong offset in source gvector.
  (test-case "gvector-append: returns gvector, not void"
    (check-pred gvector? (gvector-append (gvector 1) (gvector 2))))
  (test-case "gvector-append: contents are concatenation"
    (check-equal? (gvector->list (gvector-append (gvector 1) (gvector 2)))
                  '(1 2)))
  (test-case "gvector-append: count is sum"
    (check-equal? (gvector-count (gvector-append (gvector 1) (gvector 2)))
                  2))
  (test-case "gvector-append: empty + empty"
    (check-equal? (gvector->list (gvector-append (gvector) (gvector)))
                  '()))
  (test-case "gvector-append: doesn't modify arguments"
    (let ([a (gvector 1)] [b (gvector 2)])
      (gvector-append a b)
      (check-equal? (gvector->list a) '(1))
      (check-equal? (gvector->list b) '(2))))

  ;; Bug: for*/gvector drops inner-loop elements after the first.
  (test-case "for*/gvector: n=1 m=2 produces 2 elements"
    (check-equal? (gvector->list
                   (for*/gvector ([i (in-range 1)] [j (in-range 2)])
                     (cons i j)))
                  '((0 . 0) (0 . 1))))
  (test-case "for*/gvector: n=2 m=3 produces 6 elements"
    (check-equal? (gvector-count
                   (for*/gvector ([i (in-range 2)] [j (in-range 3)])
                     (+ (* i 3) j)))
                  6))
  (test-case "for*/gvector: contents match for*/list"
    (check-equal? (gvector->list
                   (for*/gvector ([i (in-range 3)] [j (in-range 2)])
                     (list i j)))
                  (for*/list ([i (in-range 3)] [j (in-range 2)])
                    (list i j)))))

;; ---------------------------------------------------------------------------
;; Concurrent property tests.
;;
;; These exercise the CAS retry paths in ensure-free-space! and trim!
;; which are only reachable when multiple threads race on the same
;; gvector. We compile gvector with GVECTOR_SLEEP=1 so that the
;; maybe-sleep calls widen the race window. Parallel threads (OS-level
;; parallelism) are used for true concurrency.
;;
;; Note: errortrace's register-executed-once uses non-atomic set-mcdr!,
;; so execution counts from parallel threads suffer data races and may
;; show as 0 even though the code ran. These tests verify memory safety
;; (no crashes, count consistent with contents) rather than relying on
;; errortrace coverage measurement.

(module+ concurrent
  (require rackcheck
           rackunit
           racket/list
           errortrace/errortrace-lib
           racket/path)

  (define gvector-src (collection-file-path "gvector.rkt" "data"))
  (define gvector-simplified (simplify-path gvector-src))

  ;; Build a namespace where gvector is compiled from source with
  ;; GVECTOR_SLEEP=1 (widening CAS race window) and errortrace
  ;; (so we can measure that the CAS paths get hit).
  (define ns (make-base-namespace))
  (namespace-attach-module (current-namespace) 'errortrace/errortrace-lib ns)
  (namespace-attach-module (current-namespace) 'errortrace/errortrace-key ns)

  (parameterize ([current-namespace ns])
    (namespace-require 'errortrace/errortrace-lib)
    (eval '(begin
             (execute-counts-enabled #t)
             (current-compile (make-errortrace-compile-handler))))
    (define orig-load/use-compiled (current-load/use-compiled))
    (current-load/use-compiled
     (lambda (path expected-module)
       (if (and (path? path)
                (equal? (simplify-path path) gvector-simplified))
           ;; Set GVECTOR_SLEEP=1 during compilation so maybe-sleep
           ;; expands to (sleep 0.01), widening the race window.
           (parameterize ([current-environment-variables
                           (let ([ev (environment-variables-copy
                                      (current-environment-variables))])
                             (environment-variables-set! ev #"GVECTOR_SLEEP" #"1")
                             ev)])
             ((current-load) path expected-module))
           (orig-load/use-compiled path expected-module))))
    (namespace-require 'data/gvector))

  ;; Pull out the instrumented functions
  (define-syntax-rule (get-fn name)
    (parameterize ([current-namespace ns])
      (dynamic-require 'data/gvector 'name)))

  (define make-gvector*   (get-fn make-gvector))
  (define gvector-add!*   (get-fn gvector-add!))
  (define gvector-count*  (get-fn gvector-count))
  (define gvector-ref*    (get-fn gvector-ref))
  (define gvector-remove-last!* (get-fn gvector-remove-last!))
  (define gvector->list*  (get-fn gvector->list))

  ;; --- Concurrent property: racing adds trigger CAS retry ---
  ;; Uses parallel threads (OS-level parallelism) so two threads truly
  ;; run concurrently. With GVECTOR_SLEEP=1, the sleep between reading
  ;; vec and doing the CAS gives the other thread time to install a
  ;; different vec, causing the CAS to fail and retry.

  (define-property prop:concurrent-add-cas-retry
    ([n (gen:integer-in 10 50)])
    (let ([gv (make-gvector* #:capacity 1)]
          [pool (make-parallel-thread-pool 2)])
      (define t1
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range n)])
                    (gvector-add!* gv i)))))
      (define t2
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range n)])
                    (gvector-add!* gv (+ n i))))))
      (parallel-thread-pool-close pool)
      (thread-wait t1)
      (thread-wait t2)
      ;; Memory safety: no crash, count matches readable contents.
      ;; Count may be less than (* 2 n) due to n-field races (documented
      ;; as expected — gvector is not thread-safe for count correctness).
      (let ([count (gvector-count* gv)])
        (and (> count 0)
             (= count (length (gvector->list* gv)))))))

  ;; --- Concurrent property: racing add + remove triggers trim! CAS paths ---
  ;; One thread adds elements while another removes them. The remove
  ;; path calls trim!, which does a CAS to install a smaller vector.
  ;; With GVECTOR_SLEEP=1, the add thread can slip in between trim!'s
  ;; re-read of n and its CAS, triggering the safety net on line 212.

  (define-property prop:concurrent-add-remove-trim
    ([n (gen:integer-in 20 80)])
    (let ([gv (make-gvector* #:capacity 1)]
          [pool (make-parallel-thread-pool 2)])
      (for ([i (in-range n)]) (gvector-add!* gv i))
      (define t-add
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range n)])
                    (gvector-add!* gv (+ n i))))))
      (define t-remove
        (thread #:pool pool
                (lambda ()
                  (for ([_ (in-range (quotient n 2))])
                    (with-handlers ([exn:fail? void])
                      (gvector-remove-last!* gv))))))
      (parallel-thread-pool-close pool)
      (thread-wait t-add)
      (thread-wait t-remove)
      (let ([count (gvector-count* gv)]
            [contents (gvector->list* gv)])
        (= count (length contents)))))

  ;; --- Concurrent property: many threads racing on add to same gvector ---
  ;; This maximizes contention on the CAS in define/ensure-space!.

  (define-property prop:concurrent-many-adders
    ([threads-n (gen:integer-in 2 4)]
     [items-n (gen:integer-in 5 30)])
    (let ([gv (make-gvector* #:capacity 1)]
          [pool (make-parallel-thread-pool threads-n)])
      (define threads
        (for/list ([t (in-range threads-n)])
          (thread #:pool pool
                  (lambda ()
                    (for ([i (in-range items-n)])
                      (gvector-add!* gv (+ (* t items-n) i)))))))
      (parallel-thread-pool-close pool)
      (for-each thread-wait threads)
      ;; Memory safety: no crash, count matches readable contents
      (let ([count (gvector-count* gv)])
        (and (> count 0)
             (= count (length (gvector->list* gv)))))))

  ;; --- Concurrent property: interleaved add and remove-last causes trim ---
  ;; Grow large then shrink to trigger trim!, while another thread adds.

  (define-property prop:concurrent-grow-shrink-cycle
    ([n (gen:integer-in 20 60)])
    (let ([gv (make-gvector* #:capacity 1)]
          [pool (make-parallel-thread-pool 2)])
      ;; Grow
      (for ([i (in-range n)]) (gvector-add!* gv i))
      ;; Now shrink almost to zero while adding back — in parallel
      (define t-shrink
        (thread #:pool pool
                (lambda ()
                  (for ([_ (in-range (- n 5))])
                    (with-handlers ([exn:fail? void])
                      (gvector-remove-last!* gv))))))
      (define t-grow
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range (quotient n 2))])
                    (gvector-add!* gv (+ n i))))))
      (parallel-thread-pool-close pool)
      (thread-wait t-shrink)
      (thread-wait t-grow)
      ;; Must still be consistent
      (let ([count (gvector-count* gv)]
            [contents (gvector->list* gv)])
        (= count (length contents)))))

  ;; --- Concurrent property: aggressive trim! while concurrent adds ---
  ;; This targets line 212 (trim! safety net) and line 124 (ensure-free-space!
  ;; called from the safety net). We grow the gvector large, then have one
  ;; thread aggressively remove (triggering trim!) while another adds.
  ;; The sleep in trim! gives the add thread time to push n past new-cap
  ;; after trim!'s CAS succeeds.

  ;; --- Concurrent property: aggressive trim! while parallel adds ---
  ;; Uses parallel threads to truly race. Targets line 212 (trim!
  ;; safety net) and line 124 (ensure-free-space! from safety net).
  ;; Grow large, then race: one thread removes aggressively (triggering
  ;; trim!), while another adds (pushing n past new-cap after CAS).

  (define-property prop:concurrent-trim-safety-net
    ([n (gen:integer-in 40 100)])
    (let ([gv (make-gvector* #:capacity 1)]
          [pool (make-parallel-thread-pool 2)])
      (for ([i (in-range n)]) (gvector-add!* gv i))
      (define t-remove
        (thread #:pool pool
                (lambda ()
                  (for ([_ (in-range (- n 2))])
                    (with-handlers ([exn:fail? void])
                      (gvector-remove-last!* gv))))))
      (define t-add
        (thread #:pool pool
                (lambda ()
                  (for ([i (in-range (quotient n 2))])
                    (gvector-add!* gv (+ 1000 i))))))
      (parallel-thread-pool-close pool)
      (thread-wait t-remove)
      (thread-wait t-add)
      ;; Memory safety: no crash, count is consistent
      (let ([count (gvector-count* gv)])
        (and (>= count 0)
             (= count (length (gvector->list* gv)))))))

  ;; Run the concurrent properties. Use fewer tests since each involves
  ;; thread synchronization and sleeps.
  (check-property (make-config #:tests 20 #:deadline (+ (current-inexact-milliseconds) 120000))
                  prop:concurrent-add-cas-retry)
  (check-property (make-config #:tests 20 #:deadline (+ (current-inexact-milliseconds) 120000))
                  prop:concurrent-add-remove-trim)
  (check-property (make-config #:tests 20 #:deadline (+ (current-inexact-milliseconds) 120000))
                  prop:concurrent-many-adders)
  (check-property (make-config #:tests 20 #:deadline (+ (current-inexact-milliseconds) 120000))
                  prop:concurrent-grow-shrink-cycle)
  (check-property (make-config #:tests 20 #:deadline (+ (current-inexact-milliseconds) 120000))
                  prop:concurrent-trim-safety-net)

  (printf "Concurrent property tests done.\n"))
