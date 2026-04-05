#lang racket/base

;; Property-based tests for racket/treelist.
;;
;; Covers every public API function with both model-based properties
;; (comparing treelist behavior to a reference list) and algebraic
;; properties (relating operations to each other without a model).
;;
;; Includes persistence properties verifying immutability, error path
;; properties, and a coverage-guided section.

(require rackcheck
         rackunit
         racket/treelist
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
    (gen:list (gen:tuple (gen:integer-in 0 9)
                         gen:element
                         gen:natural)
              #:max-length max-ops)))

;; ---------------------------------------------------------------------------
;; Helpers

(define (make-tl lst)
  (list->treelist lst))

;; ---------------------------------------------------------------------------
;; Model-based testing

(define (apply-operations ops)
  (define init-tl empty-treelist)
  (define init-model '())
  (let loop ([tl init-tl]
             [model init-model]
             [remaining ops])
    (cond
      [(null? remaining)
       (and (= (treelist-length tl) (length model))
            (equal? (treelist->list tl) model))]
      [else
       (define op (car remaining))
       (define selector (car op))
       (define elem (cadr op))
       (define raw-idx (caddr op))
       (define len (length model))
       (define-values (new-tl new-model)
         (cond
           [(= selector 0)
            ;; treelist-add
            (values (treelist-add tl elem)
                    (append model (list elem)))]
           [(= selector 1)
            ;; treelist-cons
            (values (treelist-cons tl elem)
                    (cons elem model))]
           [(and (= selector 2) (> len 0))
            ;; treelist-set
            (define idx (modulo raw-idx len))
            (values (treelist-set tl idx elem)
                    (list-set model idx elem))]
           [(= selector 3)
            ;; treelist-insert
            (define idx (modulo raw-idx (add1 len)))
            (values (treelist-insert tl idx elem)
                    (append (take model idx) (list elem) (drop model idx)))]
           [(and (= selector 4) (> len 0))
            ;; treelist-delete
            (define idx (modulo raw-idx len))
            (values (treelist-delete tl idx)
                    (append (take model idx) (drop model (add1 idx))))]
           [(= selector 5)
            ;; treelist-append with singleton
            (values (treelist-append tl (make-tl (list elem)))
                    (append model (list elem)))]
           [(= selector 6)
            ;; treelist-reverse
            (values (treelist-reverse tl)
                    (reverse model))]
           [(and (= selector 7) (> len 0))
            ;; treelist-rest
            (values (treelist-rest tl)
                    (cdr model))]
           [(and (= selector 8) (> len 0))
            ;; treelist-take
            (define n (modulo raw-idx (add1 len)))
            (values (treelist-take tl n)
                    (take model n))]
           [(and (= selector 9) (> len 0))
            ;; treelist-drop
            (define n (modulo raw-idx (add1 len)))
            (values (treelist-drop tl n)
                    (drop model n))]
           [else
            (values tl model)]))
       (if (and (= (treelist-length new-tl) (length new-model))
                (equal? (treelist->list new-tl) new-model))
           (loop new-tl new-model (cdr remaining))
           #f)])))

(define-property prop:model-correspondence
  ([ops (gen:operations 40)])
  (apply-operations ops))

;; =========================================================================
;; Per-function properties (model-based: compare to list)
;; =========================================================================

;; --- treelist? ---

(define-property prop:treelist?-positive
  ([lst gen:element-list])
  (treelist? (make-tl lst)))

(define-property prop:treelist?-negative
  ([lst gen:element-list])
  (and (not (treelist? lst))
       (not (treelist? (list->vector lst)))
       (not (treelist? 42))))

;; --- treelist-empty?, empty-treelist ---

(define-property prop:empty-treelist-is-empty
  ()
  (and (treelist-empty? empty-treelist)
       (= (treelist-length empty-treelist) 0)))

(define-property prop:nonempty-not-empty
  ([lst gen:nonempty-element-list])
  (not (treelist-empty? (make-tl lst))))

;; --- treelist constructor ---

(define-property prop:constructor-matches-list
  ([lst gen:element-list])
  (equal? (treelist->list (apply treelist lst)) lst))

(define-property prop:constructor-count
  ([lst gen:element-list])
  (= (treelist-length (apply treelist lst)) (length lst)))

;; --- make-treelist ---

(define-property prop:make-treelist-correct
  ([n (gen:integer-in 0 30)]
   [elem gen:element])
  (let ([tl (make-treelist n elem)])
    (and (= (treelist-length tl) n)
         (for/and ([i (in-range n)])
           (equal? (treelist-ref tl i) elem)))))

;; --- list->treelist ---

(define-property prop:list->treelist-roundtrip
  ([lst gen:element-list])
  (equal? (treelist->list (list->treelist lst)) lst))

;; --- vector->treelist ---

(define-property prop:vector->treelist-roundtrip
  ([lst gen:element-list])
  (let ([v (list->vector lst)])
    (equal? (treelist->list (vector->treelist v)) lst)))

;; --- sequence->treelist ---

(define-property prop:sequence->treelist-from-list
  ([lst gen:element-list])
  (equal? (treelist->list (sequence->treelist lst)) lst))

;; --- treelist-length ---

(define-property prop:length-consistent
  ([lst gen:element-list])
  (= (treelist-length (make-tl lst)) (length lst)))

;; --- treelist-ref ---

(define-property prop:ref-matches-list-ref
  ([lst gen:nonempty-element-list])
  (let ([tl (make-tl lst)])
    (for/and ([i (in-range (length lst))])
      (equal? (treelist-ref tl i) (list-ref lst i)))))

;; --- treelist-first, treelist-last ---

(define-property prop:first-matches
  ([lst gen:nonempty-element-list])
  (equal? (treelist-first (make-tl lst)) (first lst)))

(define-property prop:last-matches
  ([lst gen:nonempty-element-list])
  (equal? (treelist-last (make-tl lst)) (last lst)))

;; --- treelist-set ---

(define-property prop:set-matches-list-set
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [pos (modulo pos-raw (length lst))])
    (equal? (treelist->list (treelist-set tl pos elem))
            (list-set lst pos elem))))

;; --- treelist-add ---

(define-property prop:add-appends
  ([lst gen:element-list]
   [elem gen:element])
  (equal? (treelist->list (treelist-add (make-tl lst) elem))
          (append lst (list elem))))

;; --- treelist-cons ---

(define-property prop:cons-prepends
  ([lst gen:element-list]
   [elem gen:element])
  (equal? (treelist->list (treelist-cons (make-tl lst) elem))
          (cons elem lst)))

;; --- treelist-append (binary) ---

(define-property prop:append-binary-correct
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (equal? (treelist->list (treelist-append (make-tl lst1) (make-tl lst2)))
          (append lst1 lst2)))

;; --- treelist-append (variadic with 3 args) ---

(define-property prop:append-variadic-correct
  ([l1 gen:element-list]
   [l2 gen:element-list]
   [l3 gen:element-list])
  (equal? (treelist->list (treelist-append (make-tl l1) (make-tl l2) (make-tl l3)))
          (append l1 l2 l3)))

;; --- treelist-insert ---

(define-property prop:insert-correct
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([pos (modulo pos-raw (add1 (length lst)))])
    (equal? (treelist->list (treelist-insert (make-tl lst) pos elem))
            (append (take lst pos) (list elem) (drop lst pos)))))

;; --- treelist-delete ---

(define-property prop:delete-correct
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([pos (modulo pos-raw (length lst))])
    (equal? (treelist->list (treelist-delete (make-tl lst) pos))
            (append (take lst pos) (drop lst (add1 pos))))))

;; --- treelist-rest ---

(define-property prop:rest-correct
  ([lst gen:nonempty-element-list])
  (equal? (treelist->list (treelist-rest (make-tl lst)))
          (cdr lst)))

;; --- treelist-take ---

(define-property prop:take-correct
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let ([n (modulo n-raw (add1 (length lst)))])
    (equal? (treelist->list (treelist-take (make-tl lst) n))
            (take lst n))))

;; --- treelist-drop ---

(define-property prop:drop-correct
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let ([n (modulo n-raw (add1 (length lst)))])
    (equal? (treelist->list (treelist-drop (make-tl lst) n))
            (drop lst n))))

;; --- treelist-take-right ---

(define-property prop:take-right-correct
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let ([n (modulo n-raw (add1 (length lst)))])
    (equal? (treelist->list (treelist-take-right (make-tl lst) n))
            (take-right lst n))))

;; --- treelist-drop-right ---

(define-property prop:drop-right-correct
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let ([n (modulo n-raw (add1 (length lst)))])
    (equal? (treelist->list (treelist-drop-right (make-tl lst) n))
            (drop-right lst n))))

;; --- treelist-sublist ---

(define-property prop:sublist-correct
  ([lst gen:element-list]
   [a-raw gen:natural]
   [b-raw gen:natural])
  (let* ([len (length lst)]
         [a (modulo a-raw (add1 len))]
         [b (modulo b-raw (add1 len))]
         [lo (min a b)]
         [hi (max a b)])
    (equal? (treelist->list (treelist-sublist (make-tl lst) lo hi))
            (take (drop lst lo) (- hi lo)))))

;; --- treelist-reverse ---

(define-property prop:reverse-correct
  ([lst gen:element-list])
  (equal? (treelist->list (treelist-reverse (make-tl lst)))
          (reverse lst)))

;; --- treelist-map ---

(define-property prop:map-correct
  ([lst gen:nat-list])
  (equal? (treelist->list (treelist-map (make-tl lst) add1))
          (map add1 lst)))

;; --- treelist-for-each ---

(define-property prop:for-each-visits-all
  ([lst gen:element-list])
  (let ([count 0])
    (treelist-for-each (make-tl lst) (lambda (_) (set! count (add1 count))))
    (= count (length lst))))

;; --- treelist-filter ---

(define-property prop:filter-correct
  ([lst gen:nat-list])
  (equal? (treelist->list (treelist-filter even? (make-tl lst)))
          (filter even? lst)))

;; --- treelist-member? ---

(define-property prop:member?-present
  ([lst gen:nonempty-element-list])
  (let ([elem (list-ref lst (random (length lst)))])
    (treelist-member? (make-tl lst) elem)))

(define-property prop:member?-absent
  ([lst gen:nat-list])
  (not (treelist-member? (make-tl lst) 'not-a-nat-sentinel)))

;; --- treelist-find ---

(define-property prop:find-correct
  ([lst gen:nat-list])
  (let ([result (treelist-find (make-tl lst) even?)]
        [expected (for/first ([x (in-list lst)] #:when (even? x)) x)])
    (equal? result expected)))

;; --- treelist-index-of ---

(define-property prop:index-of-correct
  ([lst gen:nonempty-element-list])
  (let* ([elem (list-ref lst 0)]
         [idx (treelist-index-of (make-tl lst) elem)])
    (and idx (equal? (treelist-ref (make-tl lst) idx) elem))))

;; --- treelist-sort ---

(define-property prop:sort-correct
  ([lst gen:nat-list])
  (equal? (treelist->list (treelist-sort (make-tl lst) <))
          (sort lst <)))

;; --- treelist-flatten ---

(define-property prop:flatten-correct
  ([lsts (gen:list gen:nat-list #:max-length 10)])
  (let* ([tl-of-tls (list->treelist (map list->treelist lsts))])
    (equal? (treelist->list (treelist-flatten tl-of-tls))
            (apply append lsts))))

;; --- treelist-append* ---

(define-property prop:append*-correct
  ([lsts (gen:list gen:nat-list #:max-length 10)])
  (let* ([tl-of-tls (list->treelist (map list->treelist lsts))])
    (equal? (treelist->list (treelist-append* tl-of-tls))
            (apply append lsts))))

;; --- treelist->list ---

(define-property prop:to-list-roundtrip
  ([lst gen:element-list])
  (equal? (treelist->list (make-tl lst)) lst))

;; --- treelist->vector ---

(define-property prop:to-vector-roundtrip
  ([lst gen:element-list])
  (equal? (vector->list (treelist->vector (make-tl lst))) lst))

;; --- in-treelist ---

(define-property prop:in-treelist-matches-list
  ([lst gen:element-list])
  (equal? (for/list ([x (in-treelist (make-tl lst))]) x) lst))

;; --- for/treelist ---

(define-property prop:for/treelist-correct
  ([lst gen:element-list])
  (equal? (treelist->list (for/treelist ([x (in-list lst)]) x)) lst))

(define-property prop:for/treelist-with-filter
  ([lst gen:nat-list])
  (equal? (treelist->list (for/treelist ([x (in-list lst)]
                                         #:when (even? x))
                            x))
          (filter even? lst)))

;; --- for*/treelist ---

(define-property prop:for*/treelist-correct
  ([n (gen:integer-in 0 6)]
   [m (gen:integer-in 0 6)])
  (equal? (treelist->list (for*/treelist ([i (in-range n)]
                                          [j (in-range m)])
                            (+ (* i m) j)))
          (for*/list ([i (in-range n)]
                      [j (in-range m)])
            (+ (* i m) j))))

;; --- serialize/deserialize roundtrip ---

(define-property prop:serialize-roundtrip
  ([lst (gen:list gen:natural #:max-length 20)])
  (equal? (deserialize (serialize (make-tl lst))) (make-tl lst)))

;; --- equal? ---

(define-property prop:equal-same-contents
  ([lst gen:element-list])
  (equal? (make-tl lst) (make-tl lst)))

(define-property prop:not-equal-different-length
  ([lst gen:nonempty-element-list]
   [elem gen:element])
  (not (equal? (make-tl lst) (make-tl (cons elem lst)))))

;; --- equal-hash-code consistency ---

(define-property prop:hash-consistent-with-equal
  ([lst gen:element-list])
  (= (equal-hash-code (make-tl lst))
     (equal-hash-code (make-tl lst))))

;; =========================================================================
;; Algebraic / equational properties (non-model: relate operations)
;; =========================================================================

;; rest of cons = original
(define-property prop:rest-of-cons-identity
  ([lst gen:element-list]
   [elem gen:element])
  (let ([tl (make-tl lst)])
    (equal? (treelist-rest (treelist-cons tl elem))
            tl)))

;; delete of add at end = original
(define-property prop:delete-of-add-identity
  ([lst gen:element-list]
   [elem gen:element])
  (let ([tl (make-tl lst)])
    (equal? (treelist-delete (treelist-add tl elem) (treelist-length tl))
            tl)))

;; delete of insert = original
(define-property prop:delete-of-insert-identity
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (equal? (treelist-delete (treelist-insert tl pos elem) pos)
            tl)))

;; take ++ drop = original
(define-property prop:take-drop-append-identity
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let* ([tl (make-tl lst)]
         [n (modulo n-raw (add1 (length lst)))])
    (equal? (treelist-append (treelist-take tl n) (treelist-drop tl n))
            tl)))

;; drop-right ++ take-right = original
(define-property prop:drop-right-take-right-append-identity
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let* ([tl (make-tl lst)]
         [n (modulo n-raw (add1 (length lst)))])
    (equal? (treelist-append (treelist-drop-right tl n) (treelist-take-right tl n))
            tl)))

;; cons = insert at 0
(define-property prop:cons-is-insert-at-0
  ([lst gen:element-list]
   [elem gen:element])
  (let ([tl (make-tl lst)])
    (equal? (treelist-cons tl elem)
            (treelist-insert tl 0 elem))))

;; add = insert at end
(define-property prop:add-is-insert-at-end
  ([lst gen:element-list]
   [elem gen:element])
  (let ([tl (make-tl lst)])
    (equal? (treelist-add tl elem)
            (treelist-insert tl (treelist-length tl) elem))))

;; append is associative
(define-property prop:append-associative
  ([l1 gen:nat-list]
   [l2 gen:nat-list]
   [l3 gen:nat-list])
  (let ([a (make-tl l1)]
        [b (make-tl l2)]
        [c (make-tl l3)])
    (equal? (treelist-append (treelist-append a b) c)
            (treelist-append a b c))))

;; append right identity
(define-property prop:append-right-identity
  ([lst gen:element-list])
  (let ([tl (make-tl lst)])
    (equal? (treelist-append tl empty-treelist)
            tl)))

;; append left identity
(define-property prop:append-left-identity
  ([lst gen:element-list])
  (let ([tl (make-tl lst)])
    (equal? (treelist-append empty-treelist tl)
            tl)))

;; reverse is involution
(define-property prop:reverse-involution
  ([lst gen:element-list])
  (let ([tl (make-tl lst)])
    (equal? (treelist-reverse (treelist-reverse tl))
            tl)))

;; append length additive
(define-property prop:append-length-additive
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([a (make-tl lst1)]
        [b (make-tl lst2)])
    (= (treelist-length (treelist-append a b))
       (+ (treelist-length a) (treelist-length b)))))

;; insert increases length by 1
(define-property prop:insert-increases-length
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (= (treelist-length (treelist-insert tl pos elem))
       (add1 (treelist-length tl)))))

;; delete decreases length by 1
(define-property prop:delete-decreases-length
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([tl (make-tl lst)]
         [pos (modulo pos-raw (length lst))])
    (= (treelist-length (treelist-delete tl pos))
       (sub1 (treelist-length tl)))))

;; ref of set = new element
(define-property prop:ref-of-set
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [pos (modulo pos-raw (length lst))])
    (equal? (treelist-ref (treelist-set tl pos elem) pos)
            elem)))

;; set with current value is identity
(define-property prop:set-with-current-is-identity
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([tl (make-tl lst)]
         [pos (modulo pos-raw (length lst))])
    (equal? (treelist-set tl pos (treelist-ref tl pos))
            tl)))

;; set on different indices commutes
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
              (let ([tl (make-tl lst)])
                (equal? (treelist-set (treelist-set tl pos1 e1) pos2 e2)
                        (treelist-set (treelist-set tl pos2 e2) pos1 e1))))))))

;; set is idempotent
(define-property prop:set-idempotent
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [pos (modulo pos-raw (length lst))])
    (equal? (treelist-set tl pos elem)
            (treelist-set (treelist-set tl pos elem) pos elem))))

;; treelist->vector length = treelist-length
(define-property prop:to-vector-length-is-length
  ([lst gen:element-list])
  (let ([tl (make-tl lst)])
    (= (vector-length (treelist->vector tl))
       (treelist-length tl))))

;; treelist->list length = treelist-length
(define-property prop:to-list-length-is-length
  ([lst gen:element-list])
  (let ([tl (make-tl lst)])
    (= (length (treelist->list tl))
       (treelist-length tl))))

;; map identity = original
(define-property prop:map-identity
  ([lst gen:element-list])
  (let ([tl (make-tl lst)])
    (equal? (treelist-map tl values)
            tl)))

;; filter-all = original
(define-property prop:filter-all
  ([lst gen:element-list])
  (let ([tl (make-tl lst)])
    (equal? (treelist-filter (lambda (_) #t) tl)
            tl)))

;; filter length <= original length
(define-property prop:filter-length-leq
  ([lst gen:nat-list])
  (let ([tl (make-tl lst)])
    (<= (treelist-length (treelist-filter even? tl))
        (treelist-length tl))))

;; sort idempotent
(define-property prop:sort-idempotent
  ([lst gen:nat-list])
  (let ([tl (make-tl lst)])
    (equal? (treelist-sort (treelist-sort tl <) <)
            (treelist-sort tl <))))

;; serialize roundtrip preserves equality
(define-property prop:serialize-preserves-equality
  ([lst (gen:list gen:natural #:max-length 20)])
  (let ([tl (make-tl lst)])
    (equal? tl (deserialize (serialize tl)))))

;; =========================================================================
;; Persistence properties (immutability verification)
;; =========================================================================

(define-property prop:persistence-add
  ([lst gen:element-list]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [original (treelist->list tl)]
         [_ (treelist-add tl elem)])
    (equal? (treelist->list tl) original)))

(define-property prop:persistence-cons
  ([lst gen:element-list]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [original (treelist->list tl)]
         [_ (treelist-cons tl elem)])
    (equal? (treelist->list tl) original)))

(define-property prop:persistence-set
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [original (treelist->list tl)]
         [pos (modulo pos-raw (length lst))]
         [_ (treelist-set tl pos elem)])
    (equal? (treelist->list tl) original)))

(define-property prop:persistence-insert
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([tl (make-tl lst)]
         [original (treelist->list tl)]
         [pos (modulo pos-raw (add1 (length lst)))]
         [_ (treelist-insert tl pos elem)])
    (equal? (treelist->list tl) original)))

(define-property prop:persistence-delete
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([tl (make-tl lst)]
         [original (treelist->list tl)]
         [pos (modulo pos-raw (length lst))]
         [_ (treelist-delete tl pos)])
    (equal? (treelist->list tl) original)))

(define-property prop:persistence-append
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let* ([tl1 (make-tl lst1)]
         [tl2 (make-tl lst2)]
         [orig1 (treelist->list tl1)]
         [orig2 (treelist->list tl2)]
         [_ (treelist-append tl1 tl2)])
    (and (equal? (treelist->list tl1) orig1)
         (equal? (treelist->list tl2) orig2))))

(define-property prop:persistence-take
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let* ([tl (make-tl lst)]
         [original (treelist->list tl)]
         [n (modulo n-raw (add1 (length lst)))]
         [_ (treelist-take tl n)])
    (equal? (treelist->list tl) original)))

(define-property prop:persistence-drop
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let* ([tl (make-tl lst)]
         [original (treelist->list tl)]
         [n (modulo n-raw (add1 (length lst)))]
         [_ (treelist-drop tl n)])
    (equal? (treelist->list tl) original)))

(define-property prop:persistence-reverse
  ([lst gen:element-list])
  (let* ([tl (make-tl lst)]
         [original (treelist->list tl)]
         [_ (treelist-reverse tl)])
    (equal? (treelist->list tl) original)))

;; =========================================================================
;; Error path properties
;; =========================================================================

;; ref/set/add/length reject non-treelist
(define-property prop:ref-rejects-non-treelist
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-ref x 0)
    #f))

(define-property prop:set-rejects-non-treelist
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-set x 0 'v)
    #f))

(define-property prop:add-rejects-non-treelist
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-add x 1)
    #f))

(define-property prop:length-rejects-non-treelist
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-length x)
    #f))

;; ref rejects non-integer index
(define-property prop:ref-rejects-non-integer-index
  ([lst gen:nonempty-element-list])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-ref (make-tl lst) 'not-an-integer)
    #f))

;; ref/delete out of range
(define-property prop:ref-out-of-range-errors
  ([lst gen:element-list]
   [extra (gen:integer-in 1 10)])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-ref (make-tl lst) (+ (length lst) extra))
    #f))

(define-property prop:delete-out-of-range-errors
  ([lst gen:element-list]
   [extra (gen:integer-in 1 10)])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-delete (make-tl lst) (+ (length lst) extra))
    #f))

;; first/last/rest error on empty
(define-property prop:first-empty-errors
  ()
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-first empty-treelist)
    #f))

(define-property prop:last-empty-errors
  ()
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-last empty-treelist)
    #f))

(define-property prop:rest-empty-errors
  ()
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (treelist-rest empty-treelist)
    #f))

;; =========================================================================
;; Coverage-guided section
;; =========================================================================

(module+ guided
  (require rackcheck rackunit racket/treelist racket/list)
  (define treelist-src (collection-file-path "treelist.rkt" "racket"))
  (check-guided-property prop:model-correspondence
    #:config (make-guided-config #:max-iterations 5000
                                 #:max-time-ms 120000
                                 #:seed 42)
    #:target treelist-src)
  (printf "Guided property tests done.\n"))

;; =========================================================================
;; Test runner
;; =========================================================================

(module+ test
  ;; --- Type predicates ---
  (check-property prop:treelist?-positive)
  (check-property prop:treelist?-negative)

  ;; --- Empty ---
  (check-property prop:empty-treelist-is-empty)
  (check-property prop:nonempty-not-empty)

  ;; --- Constructors ---
  (check-property prop:constructor-matches-list)
  (check-property prop:constructor-count)
  (check-property prop:make-treelist-correct)

  ;; --- Conversions ---
  (check-property prop:list->treelist-roundtrip)
  (check-property prop:vector->treelist-roundtrip)
  (check-property prop:sequence->treelist-from-list)

  ;; --- Length ---
  (check-property prop:length-consistent)

  ;; --- Ref ---
  (check-property prop:ref-matches-list-ref)

  ;; --- First / Last ---
  (check-property prop:first-matches)
  (check-property prop:last-matches)

  ;; --- Set ---
  (check-property prop:set-matches-list-set)

  ;; --- Add ---
  (check-property prop:add-appends)

  ;; --- Cons ---
  (check-property prop:cons-prepends)

  ;; --- Append ---
  (check-property prop:append-binary-correct)
  (check-property prop:append-variadic-correct)

  ;; --- Insert ---
  (check-property prop:insert-correct)

  ;; --- Delete ---
  (check-property prop:delete-correct)

  ;; --- Rest ---
  (check-property prop:rest-correct)

  ;; --- Take / Drop / Take-right / Drop-right / Sublist ---
  (check-property prop:take-correct)
  (check-property prop:drop-correct)
  (check-property prop:take-right-correct)
  (check-property prop:drop-right-correct)
  (check-property prop:sublist-correct)

  ;; --- Reverse ---
  (check-property prop:reverse-correct)

  ;; --- Map ---
  (check-property prop:map-correct)

  ;; --- For-each ---
  (check-property prop:for-each-visits-all)

  ;; --- Filter ---
  (check-property prop:filter-correct)

  ;; --- Member? ---
  (check-property prop:member?-present)
  (check-property prop:member?-absent)

  ;; --- Find ---
  (check-property prop:find-correct)

  ;; --- Index-of ---
  (check-property prop:index-of-correct)

  ;; --- Sort ---
  (check-property prop:sort-correct)

  ;; --- Flatten ---
  (check-property prop:flatten-correct)

  ;; --- Append* ---
  (check-property prop:append*-correct)

  ;; --- Roundtrips ---
  (check-property prop:to-list-roundtrip)
  (check-property prop:to-vector-roundtrip)

  ;; --- in-treelist ---
  (check-property prop:in-treelist-matches-list)

  ;; --- for/treelist, for*/treelist ---
  (check-property prop:for/treelist-correct)
  (check-property prop:for/treelist-with-filter)
  (check-property prop:for*/treelist-correct)

  ;; --- Serialization ---
  (check-property prop:serialize-roundtrip)

  ;; --- Equality and hashing ---
  (check-property prop:equal-same-contents)
  (check-property prop:not-equal-different-length)
  (check-property prop:hash-consistent-with-equal)

  ;; --- Algebraic / equational properties ---
  (check-property prop:rest-of-cons-identity)
  (check-property prop:delete-of-add-identity)
  (check-property prop:delete-of-insert-identity)
  (check-property prop:take-drop-append-identity)
  (check-property prop:drop-right-take-right-append-identity)
  (check-property prop:cons-is-insert-at-0)
  (check-property prop:add-is-insert-at-end)
  (check-property prop:append-associative)
  (check-property prop:append-right-identity)
  (check-property prop:append-left-identity)
  (check-property prop:reverse-involution)
  (check-property prop:append-length-additive)
  (check-property prop:insert-increases-length)
  (check-property prop:delete-decreases-length)
  (check-property prop:ref-of-set)
  (check-property prop:set-with-current-is-identity)
  (check-property prop:set-different-indices-commute)
  (check-property prop:set-idempotent)
  (check-property prop:to-vector-length-is-length)
  (check-property prop:to-list-length-is-length)
  (check-property prop:map-identity)
  (check-property prop:filter-all)
  (check-property prop:filter-length-leq)
  (check-property prop:sort-idempotent)
  (check-property prop:serialize-preserves-equality)

  ;; --- Persistence properties ---
  (check-property prop:persistence-add)
  (check-property prop:persistence-cons)
  (check-property prop:persistence-set)
  (check-property prop:persistence-insert)
  (check-property prop:persistence-delete)
  (check-property prop:persistence-append)
  (check-property prop:persistence-take)
  (check-property prop:persistence-drop)
  (check-property prop:persistence-reverse)

  ;; --- Error path properties ---
  (check-property prop:ref-rejects-non-treelist)
  (check-property prop:set-rejects-non-treelist)
  (check-property prop:add-rejects-non-treelist)
  (check-property prop:length-rejects-non-treelist)
  (check-property prop:ref-rejects-non-integer-index)
  (check-property prop:ref-out-of-range-errors)
  (check-property prop:delete-out-of-range-errors)
  (check-property prop:first-empty-errors)
  (check-property prop:last-empty-errors)
  (check-property prop:rest-empty-errors)

  ;; --- Model-based with more iterations ---
  (check-property (make-config #:tests 200) prop:model-correspondence))
