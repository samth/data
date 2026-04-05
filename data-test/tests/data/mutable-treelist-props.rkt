#lang racket/base

;; Property-based tests for racket/mutable-treelist.
;;
;; Covers every public API function with both model-based properties
;; (comparing mutable-treelist behavior to a reference list) and
;; algebraic properties (relating operations to each other without
;; a model).

(require rackcheck
         rackunit
         racket/mutable-treelist
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

;; Raw operation tuples for model-based test.
(define (gen:operations max-ops)
  (gen:let ([n (gen:integer-in 1 max-ops)])
    (gen:list (gen:tuple (gen:integer-in 0 9)
                         gen:element
                         gen:natural)
              #:max-length max-ops)))

;; ---------------------------------------------------------------------------
;; Helpers

(define (make-mtl lst)
  (list->mutable-treelist lst))

;; ---------------------------------------------------------------------------
;; Model-based testing
;;
;; Operations modify the mutable-treelist in place and maintain a
;; parallel list model. Each step validates that the mutable-treelist
;; contents match the model.

(define (apply-operations ops)
  (define mtl (mutable-treelist))
  (define model '())
  (for/and ([op (in-list ops)])
    (define selector (car op))
    (define elem (cadr op))
    (define raw-idx (caddr op))
    (define len (length model))
    (cond
      ;; 0: add! at end
      [(= selector 0)
       (mutable-treelist-add! mtl elem)
       (set! model (append model (list elem)))]
      ;; 1: cons! at front
      [(= selector 1)
       (mutable-treelist-cons! mtl elem)
       (set! model (cons elem model))]
      ;; 2: set! at random index (non-empty)
      [(and (= selector 2) (> len 0))
       (define idx (modulo raw-idx len))
       (mutable-treelist-set! mtl idx elem)
       (set! model (list-set model idx elem))]
      ;; 3: insert! at random position
      [(= selector 3)
       (define idx (modulo raw-idx (add1 len)))
       (mutable-treelist-insert! mtl idx elem)
       (set! model (append (take model idx) (list elem) (drop model idx)))]
      ;; 4: delete! at random index (non-empty)
      [(and (= selector 4) (> len 0))
       (define idx (modulo raw-idx len))
       (mutable-treelist-delete! mtl idx)
       (set! model (append (take model idx) (drop model (add1 idx))))]
      ;; 5: append! with a single-element treelist
      [(= selector 5)
       (mutable-treelist-append! mtl (list->treelist (list elem)))
       (set! model (append model (list elem)))]
      ;; 6: reverse!
      [(= selector 6)
       (mutable-treelist-reverse! mtl)
       (set! model (reverse model))]
      ;; 7: take!
      [(= selector 7)
       (define n (modulo raw-idx (add1 len)))
       (mutable-treelist-take! mtl n)
       (set! model (take model n))]
      ;; 8: drop!
      [(= selector 8)
       (define n (modulo raw-idx (add1 len)))
       (mutable-treelist-drop! mtl n)
       (set! model (drop model n))]
      ;; 9: prepend! with a single-element treelist
      [(= selector 9)
       (mutable-treelist-prepend! mtl (list->treelist (list elem)))
       (set! model (cons elem model))]
      [else (void)])
    (and (= (mutable-treelist-length mtl) (length model))
         (equal? (mutable-treelist->list mtl) model))))

(define-property prop:model-correspondence
  ([ops (gen:operations 40)])
  (apply-operations ops))

;; =========================================================================
;; Per-function properties
;; =========================================================================

;; --- mutable-treelist? ---

(define-property prop:mutable-treelist?-positive
  ([lst gen:element-list])
  (mutable-treelist? (make-mtl lst)))

(define-property prop:mutable-treelist?-negative
  ([lst gen:element-list])
  (and (not (mutable-treelist? lst))
       (not (mutable-treelist? (list->vector lst)))
       (not (mutable-treelist? (list->treelist lst)))
       (not (mutable-treelist? 42))))

;; --- mutable-treelist-empty? ---

(define-property prop:empty?-on-empty
  ()
  (mutable-treelist-empty? (mutable-treelist)))

(define-property prop:empty?-on-nonempty
  ([lst gen:nonempty-element-list])
  (not (mutable-treelist-empty? (make-mtl lst))))

;; --- mutable-treelist constructor ---

(define-property prop:constructor-matches-list
  ([lst gen:element-list])
  (equal? (mutable-treelist->list (apply mutable-treelist lst)) lst))

(define-property prop:constructor-length
  ([lst gen:element-list])
  (= (mutable-treelist-length (apply mutable-treelist lst)) (length lst)))

;; --- make-mutable-treelist ---

(define-property prop:make-mutable-treelist-length
  ([n (gen:integer-in 0 30)])
  (= (mutable-treelist-length (make-mutable-treelist n #f)) n))

(define-property prop:make-mutable-treelist-fill
  ([n (gen:integer-in 0 30)]
   [elem gen:element])
  (let ([mtl (make-mutable-treelist n elem)])
    (for/and ([i (in-range n)])
      (equal? (mutable-treelist-ref mtl i) elem))))

;; --- list->mutable-treelist ---

(define-property prop:list->mtl-roundtrip
  ([lst gen:element-list])
  (equal? (mutable-treelist->list (list->mutable-treelist lst)) lst))

;; --- vector->mutable-treelist ---

(define-property prop:vector->mtl-roundtrip
  ([lst gen:element-list])
  (let ([v (list->vector lst)])
    (equal? (mutable-treelist->list (vector->mutable-treelist v))
            lst)))

;; --- treelist-copy (immutable -> mutable) ---

(define-property prop:treelist-copy-produces-mutable
  ([lst gen:element-list])
  (let* ([tl (list->treelist lst)]
         [mtl (treelist-copy tl)])
    (and (mutable-treelist? mtl)
         (equal? (mutable-treelist->list mtl) lst))))

(define-property prop:treelist-copy-independence
  ([lst gen:nonempty-element-list]
   [elem gen:element])
  (let* ([tl (list->treelist lst)]
         [mtl (treelist-copy tl)])
    (mutable-treelist-set! mtl 0 elem)
    ;; Original treelist unchanged
    (equal? (treelist->list tl) lst)))

;; --- mutable-treelist-copy ---

(define-property prop:mutable-treelist-copy-contents
  ([lst gen:element-list])
  (let* ([mtl (make-mtl lst)]
         [copy (mutable-treelist-copy mtl)])
    (and (mutable-treelist? copy)
         (equal? (mutable-treelist->list copy) lst))))

(define-property prop:mutable-treelist-copy-independence
  ([lst gen:nonempty-element-list]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [copy (mutable-treelist-copy mtl)])
    (mutable-treelist-set! copy 0 elem)
    ;; Original unchanged
    (equal? (mutable-treelist->list mtl) lst)))

;; --- mutable-treelist-length ---

(define-property prop:length-consistent
  ([lst gen:element-list])
  (= (mutable-treelist-length (make-mtl lst)) (length lst)))

(define-property prop:length-zero-when-empty
  ()
  (= (mutable-treelist-length (mutable-treelist)) 0))

(define-property prop:length-increments-on-add
  ([lst gen:element-list]
   [elem gen:element])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-add! mtl elem)
    (= (mutable-treelist-length mtl) (add1 (length lst)))))

;; --- mutable-treelist-ref ---

(define-property prop:ref-matches-list-ref
  ([lst gen:nonempty-element-list])
  (let ([mtl (make-mtl lst)])
    (for/and ([i (in-range (length lst))])
      (equal? (mutable-treelist-ref mtl i) (list-ref lst i)))))

;; --- mutable-treelist-first / mutable-treelist-last ---

(define-property prop:first-matches
  ([lst gen:nonempty-element-list])
  (equal? (mutable-treelist-first (make-mtl lst)) (first lst)))

(define-property prop:last-matches
  ([lst gen:nonempty-element-list])
  (equal? (mutable-treelist-last (make-mtl lst)) (last lst)))

;; --- mutable-treelist-set! ---

(define-property prop:set-ref-roundtrip
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (length lst))])
    (mutable-treelist-set! mtl pos elem)
    (equal? (mutable-treelist-ref mtl pos) elem)))

(define-property prop:set-doesnt-change-length
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (length lst))])
    (mutable-treelist-set! mtl pos elem)
    (= (mutable-treelist-length mtl) (length lst))))

(define-property prop:set-doesnt-change-other-elements
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (length lst))])
    (mutable-treelist-set! mtl pos elem)
    (for/and ([i (in-range (length lst))]
              #:unless (= i pos))
      (equal? (mutable-treelist-ref mtl i) (list-ref lst i)))))

;; --- mutable-treelist-add! ---

(define-property prop:add-appends
  ([lst gen:element-list]
   [elem gen:element])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-add! mtl elem)
    (equal? (mutable-treelist->list mtl) (append lst (list elem)))))

;; --- mutable-treelist-cons! ---

(define-property prop:cons-prepends
  ([lst gen:element-list]
   [elem gen:element])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-cons! mtl elem)
    (equal? (mutable-treelist->list mtl) (cons elem lst))))

;; --- mutable-treelist-insert! ---

(define-property prop:insert-preserves-others
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (mutable-treelist-insert! mtl pos elem)
    (equal? (mutable-treelist->list mtl)
            (append (take lst pos) (list elem) (drop lst pos)))))

(define-property prop:insert-increases-length
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (mutable-treelist-insert! mtl pos elem)
    (= (mutable-treelist-length mtl) (add1 (length lst)))))

;; --- mutable-treelist-delete! ---

(define-property prop:delete-preserves-others
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (length lst))])
    (mutable-treelist-delete! mtl pos)
    (equal? (mutable-treelist->list mtl)
            (append (take lst pos) (drop lst (add1 pos))))))

(define-property prop:delete-decreases-length
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (length lst))])
    (mutable-treelist-delete! mtl pos)
    (= (mutable-treelist-length mtl) (sub1 (length lst)))))

;; --- mutable-treelist-append! ---

(define-property prop:append!-with-treelist
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([mtl (make-mtl lst1)])
    (mutable-treelist-append! mtl (list->treelist lst2))
    (equal? (mutable-treelist->list mtl) (append lst1 lst2))))

(define-property prop:append!-with-mutable-treelist
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([mtl (make-mtl lst1)]
        [mtl2 (make-mtl lst2)])
    (mutable-treelist-append! mtl mtl2)
    (equal? (mutable-treelist->list mtl) (append lst1 lst2))))

(define-property prop:append!-doesnt-modify-source
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([mtl1 (make-mtl lst1)]
        [mtl2 (make-mtl lst2)])
    (mutable-treelist-append! mtl1 mtl2)
    (equal? (mutable-treelist->list mtl2) lst2)))

;; --- mutable-treelist-prepend! ---

(define-property prop:prepend!-with-treelist
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([mtl (make-mtl lst1)])
    (mutable-treelist-prepend! mtl (list->treelist lst2))
    (equal? (mutable-treelist->list mtl) (append lst2 lst1))))

(define-property prop:prepend!-with-mutable-treelist
  ([lst1 gen:element-list]
   [lst2 gen:element-list])
  (let ([mtl (make-mtl lst1)]
        [mtl2 (make-mtl lst2)])
    (mutable-treelist-prepend! mtl mtl2)
    (equal? (mutable-treelist->list mtl) (append lst2 lst1))))

;; --- mutable-treelist-take! / mutable-treelist-drop! ---

(define-property prop:take!-correct
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let* ([mtl (make-mtl lst)]
         [n (modulo n-raw (add1 (length lst)))])
    (mutable-treelist-take! mtl n)
    (equal? (mutable-treelist->list mtl) (take lst n))))

(define-property prop:drop!-correct
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let* ([mtl (make-mtl lst)]
         [n (modulo n-raw (add1 (length lst)))])
    (mutable-treelist-drop! mtl n)
    (equal? (mutable-treelist->list mtl) (drop lst n))))

;; --- mutable-treelist-take-right! / mutable-treelist-drop-right! ---

(define-property prop:take-right!-correct
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let* ([mtl (make-mtl lst)]
         [n (modulo n-raw (add1 (length lst)))])
    (mutable-treelist-take-right! mtl n)
    (equal? (mutable-treelist->list mtl) (take-right lst n))))

(define-property prop:drop-right!-correct
  ([lst gen:element-list]
   [n-raw gen:natural])
  (let* ([mtl (make-mtl lst)]
         [n (modulo n-raw (add1 (length lst)))])
    (mutable-treelist-drop-right! mtl n)
    (equal? (mutable-treelist->list mtl) (drop-right lst n))))

;; --- mutable-treelist-sublist! ---

(define-property prop:sublist!-correct
  ([lst gen:element-list]
   [a-raw gen:natural]
   [b-raw gen:natural])
  (let* ([len (length lst)]
         [a (modulo a-raw (add1 len))]
         [b (modulo b-raw (add1 (- len a)))]
         [end (+ a b)]
         [mtl (make-mtl lst)])
    (mutable-treelist-sublist! mtl a end)
    (equal? (mutable-treelist->list mtl)
            (take (drop lst a) (- end a)))))

;; --- mutable-treelist-reverse! ---

(define-property prop:reverse!-correct
  ([lst gen:element-list])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-reverse! mtl)
    (equal? (mutable-treelist->list mtl) (reverse lst))))

;; --- mutable-treelist-map! ---

(define-property prop:map!-correct
  ([lst gen:nat-list])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-map! mtl add1)
    (equal? (mutable-treelist->list mtl) (map add1 lst))))

;; --- mutable-treelist-sort! ---

(define-property prop:sort!-correct
  ([lst gen:nat-list])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-sort! mtl <)
    (equal? (mutable-treelist->list mtl) (sort lst <))))

;; --- mutable-treelist-snapshot ---

(define-property prop:snapshot-returns-treelist
  ([lst gen:element-list])
  (let* ([mtl (make-mtl lst)]
         [snap (mutable-treelist-snapshot mtl)])
    (and (treelist? snap)
         (not (mutable-treelist? snap)))))

(define-property prop:snapshot-matches-contents
  ([lst gen:element-list])
  (let* ([mtl (make-mtl lst)]
         [snap (mutable-treelist-snapshot mtl)])
    (equal? (treelist->list snap) lst)))

(define-property prop:snapshot-with-range
  ([lst gen:element-list]
   [a-raw gen:natural]
   [b-raw gen:natural])
  (let* ([len (length lst)]
         [a (modulo a-raw (add1 len))]
         [b (modulo b-raw (add1 (- len a)))]
         [end (+ a b)]
         [mtl (make-mtl lst)]
         [snap (mutable-treelist-snapshot mtl a end)])
    (equal? (treelist->list snap)
            (take (drop lst a) (- end a)))))

;; --- mutable-treelist->list ---

(define-property prop:to-list-length
  ([lst gen:element-list])
  (= (length (mutable-treelist->list (make-mtl lst))) (length lst)))

;; --- mutable-treelist->vector ---

(define-property prop:to-vector-roundtrip
  ([lst gen:element-list])
  (equal? (vector->list (mutable-treelist->vector (make-mtl lst))) lst))

(define-property prop:to-vector-length
  ([lst gen:element-list])
  (= (vector-length (mutable-treelist->vector (make-mtl lst))) (length lst)))

;; --- mutable-treelist-for-each ---

(define-property prop:for-each-visits-all
  ([lst gen:element-list])
  (let ([acc '()])
    (mutable-treelist-for-each (make-mtl lst)
                               (lambda (x) (set! acc (cons x acc))))
    (equal? (reverse acc) lst)))

;; --- mutable-treelist-member? ---

(define-property prop:member?-present
  ([lst gen:nonempty-element-list]
   [idx-raw gen:natural])
  (let* ([idx (modulo idx-raw (length lst))]
         [elem (list-ref lst idx)])
    (mutable-treelist-member? (make-mtl lst) elem)))

(define-property prop:member?-absent
  ([lst gen:nat-list])
  (not (mutable-treelist-member? (make-mtl lst) 'not-a-natural)))

;; --- mutable-treelist-find ---

(define-property prop:find-present
  ([lst gen:nat-list])
  (let ([mtl (make-mtl lst)]
        [evens (filter even? lst)])
    (if (null? evens)
        (not (mutable-treelist-find mtl even?))
        (equal? (mutable-treelist-find mtl even?) (first evens)))))

(define-property prop:find-absent
  ([lst gen:nat-list])
  (not (mutable-treelist-find (make-mtl lst) string?)))

;; --- in-mutable-treelist ---

(define-property prop:in-mutable-treelist-matches-list
  ([lst gen:element-list])
  (equal? (for/list ([x (in-mutable-treelist (make-mtl lst))]) x) lst))

(define-property prop:in-mutable-treelist-count
  ([lst gen:element-list])
  (= (for/sum ([_ (in-mutable-treelist (make-mtl lst))]) 1) (length lst)))

;; --- for/mutable-treelist ---

(define-property prop:for/mutable-treelist-correct
  ([lst gen:element-list])
  (equal? (mutable-treelist->list (for/mutable-treelist ([x (in-list lst)]) x))
          lst))

(define-property prop:for/mutable-treelist-with-filter
  ([lst gen:nat-list])
  (equal? (mutable-treelist->list
           (for/mutable-treelist ([x (in-list lst)]
                                  #:when (even? x))
             x))
          (filter even? lst)))

;; --- for*/mutable-treelist ---

(define-property prop:for*/mutable-treelist-correct
  ([n (gen:integer-in 0 6)]
   [m (gen:integer-in 0 6)])
  (equal? (mutable-treelist->list
           (for*/mutable-treelist ([i (in-range n)]
                                   [j (in-range m)])
             (+ (* i m) j)))
          (for*/list ([i (in-range n)]
                      [j (in-range m)])
            (+ (* i m) j))))

;; --- Serialization ---

(define-property prop:serialize-roundtrip
  ([lst (gen:list gen:natural #:max-length 20)])
  (equal? (mutable-treelist->list (deserialize (serialize (make-mtl lst))))
          lst))

(define-property prop:serialize-preserves-length
  ([lst (gen:list gen:natural #:max-length 20)])
  (= (mutable-treelist-length (deserialize (serialize (make-mtl lst))))
     (length lst)))

;; --- Equality and hashing ---

(define-property prop:equal-same-contents
  ([lst gen:element-list])
  (equal? (make-mtl lst) (make-mtl lst)))

(define-property prop:not-equal-different-length
  ([lst gen:nonempty-element-list]
   [elem gen:element])
  (not (equal? (make-mtl lst) (make-mtl (cons elem lst)))))

(define-property prop:not-equal-different-contents
  ([lst gen:nonempty-element-list]
   [elem gen:element])
  (let ([mtl1 (make-mtl lst)]
        [mtl2 (make-mtl lst)])
    (mutable-treelist-set! mtl2 0 (list 'unique-sentinel elem))
    (not (equal? mtl1 mtl2))))

(define-property prop:hash-consistent-with-equal
  ([lst gen:element-list])
  (= (equal-hash-code (make-mtl lst))
     (equal-hash-code (make-mtl lst))))

;; =========================================================================
;; Algebraic / equational properties
;; =========================================================================

;; add! then delete! last = original contents
(define-property prop:add-delete-last-identity
  ([lst gen:element-list]
   [elem gen:element])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-add! mtl elem)
    (mutable-treelist-delete! mtl (sub1 (mutable-treelist-length mtl)))
    (equal? (mutable-treelist->list mtl) lst)))

;; cons! then delete! 0 = original contents
(define-property prop:cons-delete-0-identity
  ([lst gen:element-list]
   [elem gen:element])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-cons! mtl elem)
    (mutable-treelist-delete! mtl 0)
    (equal? (mutable-treelist->list mtl) lst)))

;; insert! then delete! at same position = original contents
(define-property prop:insert-delete-identity
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (mutable-treelist-insert! mtl pos elem)
    (mutable-treelist-delete! mtl pos)
    (equal? (mutable-treelist->list mtl) lst)))

;; append! associative: (a ++ b) ++ c = a ++ (b ++ c)
(define-property prop:append!-associative
  ([l1 gen:nat-list]
   [l2 gen:nat-list]
   [l3 gen:nat-list])
  (let ([mtl-left (make-mtl l1)]
        [mtl-right (make-mtl l1)])
    ;; left: (l1 ++ l2) ++ l3
    (mutable-treelist-append! mtl-left (list->treelist l2))
    (mutable-treelist-append! mtl-left (list->treelist l3))
    ;; right: l1 ++ (l2 ++ l3)
    (let ([tl23 (list->treelist (append l2 l3))])
      (mutable-treelist-append! mtl-right tl23))
    (equal? (mutable-treelist->list mtl-left)
            (mutable-treelist->list mtl-right))))

;; append! right identity: append! with empty = no change
(define-property prop:append!-right-identity
  ([lst gen:element-list])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-append! mtl (treelist))
    (equal? (mutable-treelist->list mtl) lst)))

;; prepend! left identity: prepend! empty = no change
(define-property prop:prepend!-left-identity
  ([lst gen:element-list])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-prepend! mtl (treelist))
    (equal? (mutable-treelist->list mtl) lst)))

;; set! on different indices commutes
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
              (let ([mtl1 (make-mtl lst)]
                    [mtl2 (make-mtl lst)])
                (mutable-treelist-set! mtl1 pos1 e1)
                (mutable-treelist-set! mtl1 pos2 e2)
                (mutable-treelist-set! mtl2 pos2 e2)
                (mutable-treelist-set! mtl2 pos1 e1)
                (equal? mtl1 mtl2)))))))

;; add! equivalent to insert! at end
(define-property prop:add-is-insert-at-end
  ([lst gen:element-list]
   [elem gen:element])
  (let ([mtl1 (make-mtl lst)]
        [mtl2 (make-mtl lst)])
    (mutable-treelist-add! mtl1 elem)
    (mutable-treelist-insert! mtl2 (length lst) elem)
    (equal? (mutable-treelist->list mtl1)
            (mutable-treelist->list mtl2))))

;; cons! equivalent to insert! at 0
(define-property prop:cons-is-insert-at-0
  ([lst gen:element-list]
   [elem gen:element])
  (let ([mtl1 (make-mtl lst)]
        [mtl2 (make-mtl lst)])
    (mutable-treelist-cons! mtl1 elem)
    (mutable-treelist-insert! mtl2 0 elem)
    (equal? (mutable-treelist->list mtl1)
            (mutable-treelist->list mtl2))))

;; double reverse! = identity
(define-property prop:double-reverse-identity
  ([lst gen:element-list])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-reverse! mtl)
    (mutable-treelist-reverse! mtl)
    (equal? (mutable-treelist->list mtl) lst)))

;; length increases by 1 on add!/cons!/insert!
(define-property prop:length-increases-on-cons
  ([lst gen:element-list]
   [elem gen:element])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-cons! mtl elem)
    (= (mutable-treelist-length mtl) (add1 (length lst)))))

(define-property prop:length-increases-on-insert
  ([lst gen:element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (add1 (length lst)))])
    (mutable-treelist-insert! mtl pos elem)
    (= (mutable-treelist-length mtl) (add1 (length lst)))))

;; length decreases by 1 on delete!
(define-property prop:length-decreases-on-delete
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (length lst))])
    (mutable-treelist-delete! mtl pos)
    (= (mutable-treelist-length mtl) (sub1 (length lst)))))

;; set! doesn't change length
(define-property prop:set-preserves-length
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [pos (modulo pos-raw (length lst))])
    (mutable-treelist-set! mtl pos elem)
    (= (mutable-treelist-length mtl) (length lst))))

;; set! idempotent
(define-property prop:set-idempotent
  ([lst gen:nonempty-element-list]
   [pos-raw gen:natural]
   [elem gen:element])
  (let* ([mtl1 (make-mtl lst)]
         [mtl2 (make-mtl lst)]
         [pos (modulo pos-raw (length lst))])
    (mutable-treelist-set! mtl1 pos elem)
    (mutable-treelist-set! mtl2 pos elem)
    (mutable-treelist-set! mtl2 pos elem)
    (equal? mtl1 mtl2)))

;; (vector-length (mutable-treelist->vector mtl)) = length
(define-property prop:to-vector-length-is-length
  ([lst gen:element-list])
  (let ([mtl (make-mtl lst)])
    (= (vector-length (mutable-treelist->vector mtl))
       (mutable-treelist-length mtl))))

;; (length (mutable-treelist->list mtl)) = length
(define-property prop:to-list-length-is-length
  ([lst gen:element-list])
  (let ([mtl (make-mtl lst)])
    (= (length (mutable-treelist->list mtl))
       (mutable-treelist-length mtl))))

;; map! with values = identity
(define-property prop:map!-identity
  ([lst gen:element-list])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-map! mtl values)
    (equal? (mutable-treelist->list mtl) lst)))

;; sort! idempotent
(define-property prop:sort!-idempotent
  ([lst gen:nat-list])
  (let ([mtl (make-mtl lst)])
    (mutable-treelist-sort! mtl <)
    (define after-first (mutable-treelist->list mtl))
    (mutable-treelist-sort! mtl <)
    (equal? (mutable-treelist->list mtl) after-first)))

;; =========================================================================
;; Mutation-specific properties
;; =========================================================================

;; Snapshot isolation: mutating mtl after snapshot doesn't change snapshot
(define-property prop:snapshot-isolation
  ([lst gen:nonempty-element-list]
   [elem gen:element])
  (let* ([mtl (make-mtl lst)]
         [snap (mutable-treelist-snapshot mtl)])
    (mutable-treelist-set! mtl 0 elem)
    (mutable-treelist-add! mtl elem)
    (equal? (treelist->list snap) lst)))

;; add then remove all = empty
(define-property prop:add-remove-all-empty
  ([lst gen:element-list])
  (let ([mtl (mutable-treelist)])
    (for ([x (in-list lst)]) (mutable-treelist-add! mtl x))
    (for ([_ (in-range (length lst))])
      (mutable-treelist-delete! mtl (sub1 (mutable-treelist-length mtl))))
    (and (= (mutable-treelist-length mtl) 0)
         (equal? (mutable-treelist->list mtl) '()))))

;; alternating add!/delete! matches model
(define-property prop:alternating-add-delete
  ([adds (gen:list gen:element #:max-length 20)]
   [removes (gen:list gen:boolean #:max-length 20)])
  (let ([mtl (mutable-treelist)]
        [model '()])
    (for ([a (in-list adds)]
          [should-remove? (in-list removes)])
      (mutable-treelist-add! mtl a)
      (set! model (append model (list a)))
      (when (and should-remove? (> (length model) 0))
        (mutable-treelist-delete! mtl (sub1 (mutable-treelist-length mtl)))
        (set! model (drop-right model 1))))
    (equal? (mutable-treelist->list mtl) model)))

;; =========================================================================
;; Error path properties
;; =========================================================================

(define-property prop:ref-rejects-non-mutable-treelist
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-ref x 0)
    #f))

(define-property prop:set-rejects-non-mutable-treelist
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-set! x 0 'v)
    #f))

(define-property prop:add-rejects-non-mutable-treelist
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-add! x 1)
    #f))

(define-property prop:length-rejects-non-mutable-treelist
  ([x gen:natural])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-length x)
    #f))

(define-property prop:ref-rejects-non-integer-index
  ([lst gen:nonempty-element-list])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-ref (make-mtl lst) 'not-an-integer)
    #f))

(define-property prop:ref-out-of-range-errors
  ([lst gen:element-list]
   [extra (gen:integer-in 1 10)])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-ref (make-mtl lst) (+ (length lst) extra))
    #f))

(define-property prop:delete-out-of-range-errors
  ([lst gen:element-list]
   [extra (gen:integer-in 1 10)])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-delete! (make-mtl lst) (+ (length lst) extra))
    #f))

(define-property prop:first-errors-on-empty
  ()
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-first (mutable-treelist))
    #f))

(define-property prop:last-errors-on-empty
  ()
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (mutable-treelist-last (mutable-treelist))
    #f))

(define-property prop:make-mutable-treelist-rejects-negative
  ([n (gen:integer-in 1 100)])
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (make-mutable-treelist (- n) 0)
    #f))

;; =========================================================================
;; Test runner
;; =========================================================================

(module+ test
  ;; Type predicates
  (check-property prop:mutable-treelist?-positive)
  (check-property prop:mutable-treelist?-negative)
  (check-property prop:empty?-on-empty)
  (check-property prop:empty?-on-nonempty)

  ;; Constructors
  (check-property prop:constructor-matches-list)
  (check-property prop:constructor-length)
  (check-property prop:make-mutable-treelist-length)
  (check-property prop:make-mutable-treelist-fill)

  ;; Conversions
  (check-property prop:list->mtl-roundtrip)
  (check-property prop:vector->mtl-roundtrip)
  (check-property prop:treelist-copy-produces-mutable)
  (check-property prop:treelist-copy-independence)
  (check-property prop:mutable-treelist-copy-contents)
  (check-property prop:mutable-treelist-copy-independence)

  ;; Length
  (check-property prop:length-consistent)
  (check-property prop:length-zero-when-empty)
  (check-property prop:length-increments-on-add)

  ;; Ref
  (check-property prop:ref-matches-list-ref)

  ;; First / Last
  (check-property prop:first-matches)
  (check-property prop:last-matches)

  ;; Set
  (check-property prop:set-ref-roundtrip)
  (check-property prop:set-doesnt-change-length)
  (check-property prop:set-doesnt-change-other-elements)

  ;; Add / Cons
  (check-property prop:add-appends)
  (check-property prop:cons-prepends)

  ;; Insert
  (check-property prop:insert-preserves-others)
  (check-property prop:insert-increases-length)

  ;; Delete
  (check-property prop:delete-preserves-others)
  (check-property prop:delete-decreases-length)

  ;; Append / Prepend
  (check-property prop:append!-with-treelist)
  (check-property prop:append!-with-mutable-treelist)
  (check-property prop:append!-doesnt-modify-source)
  (check-property prop:prepend!-with-treelist)
  (check-property prop:prepend!-with-mutable-treelist)

  ;; Take / Drop
  (check-property prop:take!-correct)
  (check-property prop:drop!-correct)
  (check-property prop:take-right!-correct)
  (check-property prop:drop-right!-correct)
  (check-property prop:sublist!-correct)

  ;; Reverse
  (check-property prop:reverse!-correct)

  ;; Map / Sort
  (check-property prop:map!-correct)
  (check-property prop:sort!-correct)

  ;; Snapshot
  (check-property prop:snapshot-returns-treelist)
  (check-property prop:snapshot-matches-contents)
  (check-property prop:snapshot-with-range)

  ;; Conversions to list / vector
  (check-property prop:to-list-length)
  (check-property prop:to-vector-roundtrip)
  (check-property prop:to-vector-length)

  ;; For-each, member?, find
  (check-property prop:for-each-visits-all)
  (check-property prop:member?-present)
  (check-property prop:member?-absent)
  (check-property prop:find-present)
  (check-property prop:find-absent)

  ;; Iteration
  (check-property prop:in-mutable-treelist-matches-list)
  (check-property prop:in-mutable-treelist-count)
  (check-property prop:for/mutable-treelist-correct)
  (check-property prop:for/mutable-treelist-with-filter)
  (check-property prop:for*/mutable-treelist-correct)

  ;; Serialization
  (check-property prop:serialize-roundtrip)
  (check-property prop:serialize-preserves-length)

  ;; Equality and hashing
  (check-property prop:equal-same-contents)
  (check-property prop:not-equal-different-length)
  (check-property prop:not-equal-different-contents)
  (check-property prop:hash-consistent-with-equal)

  ;; Algebraic properties
  (check-property prop:add-delete-last-identity)
  (check-property prop:cons-delete-0-identity)
  (check-property prop:insert-delete-identity)
  (check-property prop:append!-associative)
  (check-property prop:append!-right-identity)
  (check-property prop:prepend!-left-identity)
  (check-property prop:set-different-indices-commute)
  (check-property prop:add-is-insert-at-end)
  (check-property prop:cons-is-insert-at-0)
  (check-property prop:double-reverse-identity)
  (check-property prop:length-increases-on-cons)
  (check-property prop:length-increases-on-insert)
  (check-property prop:length-decreases-on-delete)
  (check-property prop:set-preserves-length)
  (check-property prop:set-idempotent)
  (check-property prop:to-vector-length-is-length)
  (check-property prop:to-list-length-is-length)
  (check-property prop:map!-identity)
  (check-property prop:sort!-idempotent)

  ;; Mutation-specific
  (check-property prop:snapshot-isolation)
  (check-property prop:add-remove-all-empty)
  (check-property prop:alternating-add-delete)

  ;; Error paths
  (check-property prop:ref-rejects-non-mutable-treelist)
  (check-property prop:set-rejects-non-mutable-treelist)
  (check-property prop:add-rejects-non-mutable-treelist)
  (check-property prop:length-rejects-non-mutable-treelist)
  (check-property prop:ref-rejects-non-integer-index)
  (check-property prop:ref-out-of-range-errors)
  (check-property prop:delete-out-of-range-errors)
  (check-property prop:first-errors-on-empty)
  (check-property prop:last-errors-on-empty)
  (check-property prop:make-mutable-treelist-rejects-negative)

  ;; Model-based with more iterations
  (check-property (make-config #:tests 200) prop:model-correspondence))

;; ---------------------------------------------------------------------------
;; Coverage-guided section

(module+ guided
  (require rackcheck rackunit racket/mutable-treelist racket/treelist racket/list)
  (define mtl-src (collection-file-path "mutable-treelist.rkt" "racket"))
  (check-guided-property prop:model-correspondence
    #:config (make-guided-config #:max-iterations 5000
                                 #:max-time-ms 120000
                                 #:seed 42)
    #:target mtl-src)
  (printf "Guided property tests done.\n"))
