#lang racket/base
;; written by ryanc

;; Memory-safety invariant:
;;
;; For every gvector gv, at every observable point in time:
;;   (<= (gvector-n gv) (vector-length (gvector-vec gv)))
;;
;; This data structure is NOT thread-safe: concurrent mutation may
;; lose updates or produce incorrect results. However, the invariant
;; above ensures that concurrent access cannot cause memory-safety
;; violations (out-of-bounds reads via unsafe-vector*-ref).
;;
;; The invariant is maintained by ordering field updates and using CAS:
;;
;; - Growing (gvector-add!, gvector-insert!, gvector-append!):
;;   Update vec first (to a larger vector), then update n.
;;   Any concurrent reader sees the old (smaller) n with the new
;;   (larger) vec, so the invariant holds.
;;
;; - Shrinking (gvector-remove! + trim!):
;;   Update n first (to a smaller value), then update vec.
;;   Any concurrent reader sees the new (smaller) n with the old
;;   (larger) vec, so the invariant holds.
;;
;; - CAS on vec (unsafe-struct*-cas! gv 0 old-vec new-vec):
;;   When growing, define/ensure-space! uses CAS to install the new
;;   vector. If another thread replaced vec concurrently (e.g. two
;;   concurrent gvector-add! calls both creating new vectors), the
;;   CAS fails and the operation retries with the current vec.
;;   Without CAS, thread T1 could install a small vector while T2
;;   installs a large n, violating the invariant.
;;   Similarly, trim! uses CAS when installing a smaller vector.
;;
;; - n re-read in trim!:
;;   trim! re-reads n before creating the smaller vector. If n has
;;   grown past the target capacity (from concurrent adds that didn't
;;   need to resize vec), trim! aborts. After CAS succeeds, trim!
;;   checks again and grows back via ensure-free-space! if needed.
(require (for-syntax racket/base
                     syntax/contract
                     syntax/for-body)
	 racket/performance-hint
         racket/serialize
         racket/fixnum
         racket/contract/base
         racket/dict
	 racket/unsafe/ops
         racket/vector
         racket/struct)

(struct gvector (vec n)
  #:mutable
  ;; nothing subtypes a gvector, and the predicate runs on every
  ;; operation; sealing turns its walk of the type's ancestry into one
  ;; comparison.  Not `#:authentic`: `gvector-set!` handles an
  ;; impersonated gvector, so they have to remain possible.
  #:sealed
  #:property prop:dict/contract
             ;; These name the operations, which name the struct's accessors,
             ;; so they have to be wrapped for the struct to be defined first --
             ;; a property value is evaluated where it is written.
             (list (vector-immutable (case-lambda
                                       [(gv i) (gvector-ref gv i)]
                                       [(gv i d) (gvector-ref gv i d)])
                                     (lambda (gv i v) (gvector-set! gv i v))
                                     #f ;; set
                                     (lambda (gv i) (gvector-remove! gv i))
                                     #f ;; remove
                                     (lambda (gv) (gvector-count gv))
                                     (lambda (gv) (gvector-iterate-first gv))
                                     (lambda (gv it) (gvector-iterate-next gv it))
                                     (lambda (gv it) (gvector-iterate-key gv it))
                                     (lambda (gv it) (gvector-iterate-value gv it)))
                   (vector-immutable exact-nonnegative-integer?
                                     any/c
                                     exact-nonnegative-integer?
                                     #f #f #f))
  #:methods gen:equal+hash
  [(define (equal-proc x y recursive-equal?)
     (let ([vx (gvector-vec x)]
           [vy (gvector-vec y)]
           [nx (gvector-n x)]
           [ny (gvector-n y)])
       (and (= nx ny)
            (for/and ([index (in-range nx)])
              (recursive-equal? (vector-ref vx index)
                                (vector-ref vy index))))))
   (define (hash-code x hc)
     (let ([v (gvector-vec x)]
           [n (gvector-n x)])
       (for/fold ([h 1]) ([i (in-range n)])
         ;; FIXME: better way of combining hashcodes
         (+ h (hc (vector-ref v i))))))
   (define hash-proc  hash-code)
   (define hash2-proc hash-code)]
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (obj) 'gvector)
      (lambda (obj) (gvector->list obj))))]
  #:property prop:sequence (lambda (gv) (in-gvector gv))
  #:property prop:serializable
  (make-serialize-info
   (λ (this)
     (vector (gvector->vector this)))
   (cons 'deserialize-gvector (module-path-index-join '(submod data/gvector deserialize) #f))
   #t
   (or (current-load-relative-directory) (current-directory))))

;; When the environment variable GVECTOR_SLEEP is set at compile time,
;; (maybe-sleep tag) expands to (sleep 0.01), widening the race window
;; at the specified point so stress tests can exercise CAS retry paths.
;; GVECTOR_SLEEP=1 activates all sleep points; GVECTOR_SLEEP=tag
;; activates only the matching point. When unset, expands to (void).
(define-syntax (maybe-sleep stx)
  (syntax-case stx ()
    [(_ tag)
     (let ([env (getenv "GVECTOR_SLEEP")])
       (if (and env
                (or (equal? env "1")
                    (equal? env (symbol->string (syntax-e #'tag)))))
           #'(sleep 0.01)
           #'(void)))]))

;; Like maybe-sleep but with a longer duration, for points where the
;; concurrent operation itself contains a maybe-sleep.
(define-syntax (maybe-sleep/long stx)
  (syntax-case stx ()
    [(_ tag)
     (let ([env (getenv "GVECTOR_SLEEP")])
       (if (and env
                (or (equal? env "1")
                    (equal? env (symbol->string (syntax-e #'tag)))))
           #'(sleep 0.1)
           #'(void)))]))

(define DEFAULT-CAPACITY 10)

(define MIN-CAPACITY 8)

(define (make-gvector #:capacity [capacity DEFAULT-CAPACITY])
  (unless (exact-nonnegative-integer? capacity)
    (raise-argument-error* 'make-gvector 'data/gvector "exact-nonnegative-integer?" capacity))
  (gvector (make-vector (max capacity MIN-CAPACITY) 0) 0))

(define gvector*
  (let ([gvector
         (lambda init-elements
           (let ([gv (make-gvector)])
             (apply gvector-add! gv init-elements)
             gv))])
    gvector))

(define (check-index who gv index set-to-add?)
  ;; if set-to-add?, the valid indexes include one past the current end
  (define n (gvector-n gv))
  (define hi (if set-to-add? (add1 n) n))
  (unless (< index hi)
    (raise-range-error who "gvector" "" index gv 0 (sub1 hi))))

(begin-encourage-inline

  (define (check-gvector who gv)
    (unless (gvector? gv)
      (raise-argument-error* who 'data/gvector "gvector?" gv)))


  ;; grow-vec : Vector Nat Nat -> Vector/#f
  ;; Returns a new, larger vector if more space is needed, or #f if
  ;; the existing vector has enough capacity.
  (define (grow-vec vec n needed-free-space)
    (define cap (unsafe-vector*-length vec))
    (define needed-cap (unsafe-fx+ n needed-free-space))
    (cond [(unsafe-fx<= needed-cap cap) #f]
	  [else
	   ;; taken from Rust's raw_vec implementation
	   (let* ([new-cap (unsafe-fxmax (unsafe-fx* 2 cap) needed-cap)]
		  [new-cap (unsafe-fxmax new-cap MIN-CAPACITY)])
	     (vector*-extend vec new-cap 0))]))

  ;; ensure-free-space! : GVector Nat -> Void
  ;; Ensures the gvector's vec has room for needed-free-space more
  ;; elements beyond the current n. Uses CAS to install the new vector
  ;; so that concurrent growers don't clobber each other.
  (define (ensure-free-space! gv needed-free-space)
    (let loop ()
      (define v (gvector-vec gv))
      (maybe-sleep ensure-space) ; widen window for concurrent growers
      (define new-v (grow-vec v (gvector-n gv) needed-free-space))
      (when new-v
	;; CAS: only install if vec hasn't been replaced by another thread.
	;; If CAS fails, another thread installed a different vec; retry
	;; to check if the new vec is big enough.
	(unless (unsafe-struct*-cas! gv 0 v new-v)
	  (loop)))))

  ;; define/ensure-space! : binds n and v after ensuring the gvector
  ;; has room. Uses CAS on vec so concurrent ensure-space! calls
  ;; don't clobber each other.
  (define-syntax-rule (define/ensure-space! (n v) gv needed-free-space)
    (begin (define n (gvector-n gv))
	   (define v
	     (let loop ([v1 (gvector-vec gv)])
	       (maybe-sleep ensure-space) ; widen window for concurrent growers
	       (define v2 (grow-vec v1 n needed-free-space))
	       (cond [(not v2) v1]   ; already big enough
		     ;; CAS: install new vec, retry if another thread changed it
		     [(unsafe-struct*-cas! gv 0 v1 v2) v2]
		     [else (loop (gvector-vec gv))])))))

  ;; only safe on unchaperoned gvectors
  (define (unsafe-gvector-add! gv item)
    (define/ensure-space! (n v) gv 1)
    (unsafe-vector*-set! v n item)
    ;; Invariant (1): vec is already large enough (set by define/ensure-space!),
    ;; so updating n maintains n <= vector-length(vec).
    (set-gvector-n! gv (unsafe-fx+ 1 n)))

  (define gvector-add!
    (case-lambda
      [(gv item)
       (check-gvector 'gvector-add! gv)
       (define/ensure-space! (n v) gv 1)
       (unsafe-vector*-set! v n item)
       (set-gvector-n! gv (unsafe-fx+ 1 n))]
      [(gv . items)
       (check-gvector 'gvector-add! gv)
       (define item-count (length items))
       (define/ensure-space! (n v) gv item-count)
       (for ([index (in-naturals n)] [item (in-list items)])
	 (unsafe-vector*-set! v index item))
       (set-gvector-n! gv (+ n item-count))])))

;; SLOW!
(define (gvector-insert! gv index item)
  ;; This does (n - index) redundant copies on resize, but that
  ;; happens rarely and I prefer the simpler code.
  (check-gvector 'gvector-insert! gv)
  (check-index 'gvector-insert! gv index #t)
  (define/ensure-space! (n v) gv 1)
  (vector-copy! v (add1 index) v index n)
  (vector-set! v index item)
  (set-gvector-n! gv (add1 n)))

;; Shrink when vector length is > SHRINK-ON-FACTOR * #elements
(define SHRINK-ON-FACTOR 4)
;; ... unless it would shrink to less than SHRINK-MIN
(define SHRINK-MIN 10)

;; Shrink by SHRINK-BY-FACTOR
(define SHRINK-BY-FACTOR 2)

(define (trim! gv)
  ;; Invariant (1): n has already been decremented before calling trim!,
  ;; so installing a smaller vec maintains n <= vector-length(vec),
  ;; provided n hasn't grown since we read it. We re-read n before
  ;; creating the new vec to abort if concurrent adds have grown n past
  ;; our target capacity. After CAS, we verify the invariant and grow
  ;; back if a concurrent add slipped through.
  (let loop ()
    (define n0 (gvector-n gv))
    (define v (gvector-vec gv))
    (maybe-sleep trim) ; widen window for concurrent add/trim
    (define cap (vector-length v))
    (define new-cap
      (let shrink ([new-cap cap])
	(cond [(and (>= new-cap (* SHRINK-ON-FACTOR n0))
		    (>= (quotient new-cap SHRINK-BY-FACTOR) SHRINK-MIN))
	       (shrink (quotient new-cap SHRINK-BY-FACTOR))]
	      [else new-cap])))
    (when (< new-cap cap)
      ;; Re-read n: if concurrent adds grew n past new-cap, abort.
      (define n (gvector-n gv))
      (when (<= n new-cap)
	(define new-v (make-vector new-cap #f))
	(vector-copy! new-v 0 v 0 n)
	;; CAS: only install smaller vec if no other thread replaced vec
	(when (unsafe-struct*-cas! gv 0 v new-v)
	  ;; Safety net: if a concurrent add pushed n past new-cap
	  ;; between our re-read and the CAS, grow back immediately.
	  ;; The trim-safety sleep is longer than other sleep points
	  ;; so a concurrent add (which itself sleeps in ensure-space)
	  ;; has time to complete and push n past new-cap.
	  (maybe-sleep/long trim-safety)
	  (when (> (gvector-n gv) new-cap)
	    (ensure-free-space! gv 0)))))))

;; SLOW!
(define (gvector-remove! gv index)
  (check-gvector 'gvector-remove! gv)
  (define n (gvector-n gv))
  (define v (gvector-vec gv))
  (check-index 'gvector-remove! gv index #f)
  (vector-copy! v index v (add1 index) n)
  (vector-set! v (sub1 n) #f)
  (set-gvector-n! gv (sub1 n))
  (trim! gv))

(define (gvector-remove-last! gv)
  (check-gvector 'gvector-remove-last! gv)
  (let ([n (gvector-n gv)]
        [v (gvector-vec gv)])
    (unless (> n 0) (error 'gvector-remove-last! "empty"))
    (define last-val (vector-ref v (sub1 n)))
    (gvector-remove! gv (sub1 n))
    last-val))

(define (gvector-count gv)
  (check-gvector 'gvector-count gv)
  (gvector-n gv))

(define none (gensym 'none))

(define (gvector-ref gv index [default none])
  (check-gvector 'gvector-ref gv)
  (unless (exact-nonnegative-integer? index)
    (raise-type-error 'gvector-ref "exact nonnegative integer" index))
  (let ([v (gvector-vec gv)])
    (maybe-sleep ref) ; widen window for concurrent remove/trim
    (if (< index (gvector-n gv))
        (unsafe-vector*-ref v index)
        (cond [(eq? default none)
               (check-index 'gvector-ref gv index #f)]
              [(procedure? default) (default)]
              [else default]))))

(define (gvector-append! gv gv*)
  (check-gvector 'gvector-append! gv)
  (check-gvector 'gvector-append! gv*)
  (define n* (gvector-n gv*))
  (define/ensure-space! (n v) gv n*)
  (vector-copy! v n (gvector-vec gv*) 0 n*)
  (set-gvector-n! gv (+ n n*)))

(define (gvector-append gv gv*)
  (check-gvector 'gvector-append gv)
  (check-gvector 'gvector-append gv*)
  ;; retain the spare capacity of gv*
  (define gv0 (make-gvector #:capacity (+ (gvector-n gv) (vector-length (gvector-vec gv*)))))
  (define v0 (gvector-vec gv0))
  (vector-copy! v0 0 (gvector-vec gv) 0 (gvector-n gv))
  (vector-copy! v0 (gvector-n gv) (gvector-vec gv*) (gvector-n gv*)))


;; gvector-set! with index = |gv| is interpreted as gvector-add!
(define (gvector-set! gv index item)
  (check-gvector 'gvector-set! gv)
  (let ([v (gvector-vec gv)]
        [n (gvector-n gv)])
    (check-index 'gvector-set! gv index #t)
    (if (unsafe-fx= index n)
        (if (impersonator? gv)
            (gvector-add! gv item)
            (unsafe-gvector-add! gv item))
        (unsafe-vector*-set! v index item))))

;; creates a snapshot vector
(define (gvector->vector gv)
  (check-gvector 'gvector->vector gv)
  (vector*-copy (gvector-vec gv) 0 (gvector-n gv)))

(define (gvector->list gv)
  (check-gvector 'gvector->list gv)
  (vector->list (gvector->vector gv)))

;; constructs a gvector
(define (vector->gvector v)
  (unless (vector? v)
    (raise-argument-error* vector->gvector 'data/gvector "vector?" v))
  (define lv (vector-length v))
  (define gv (make-gvector #:capacity (max lv DEFAULT-CAPACITY)))
  (define nv (gvector-vec gv))
  (vector-copy! nv 0 v)
  (set-gvector-n! gv lv)
  gv)

(define (list->gvector v)
  (unless (list? v)
    (raise-argument-error* list->gvector 'data/gvector "list?" v))
  (vector->gvector (list->vector v)))

;; Iteration methods

;; A gvector position is represented as an exact-nonnegative-integer.

(define (gvector-iterate-first gv)
  (and (positive? (gvector-n gv)) 0))

(define (gvector-iterate-next gv iter)
  (check-index 'gvector-iterate-next gv iter #f)
  (let ([n (gvector-n gv)])
    (and (< (unsafe-fx+ 1 iter) n)
         (unsafe-fx+ 1 iter))))

(define (gvector-iterate-key gv iter)
  (check-index 'gvector-iterate-key gv iter #f)
  iter)

(define (gvector-iterate-value gv iter)
  (check-index 'gvector-iterate-value gv iter #f)
  (gvector-ref gv iter))

(define (in-gvector gv)
  (check-gvector 'in-gvector gv)
  (in-dict-values gv))

(define-sequence-syntax in-gvector*
  (lambda () #'in-gvector)
  (lambda (stx)
    (syntax-case stx ()
      [[(var) (in-gv gv-expr)]
       (with-syntax ([gv-expr-c (wrap-expr/c #'gvector? #'gv-expr #:macro #'in-gv)])
         (syntax/loc stx
           [(var)
            (:do-in ([(gv) gv-expr-c])
                    (void) ;; outer-check; handled by contract
                    ([index 0] [vec (gvector-vec gv)] [n (gvector-n gv)]) ;; loop bindings
                    (unsafe-fx< index n) ;; pos-guard
                    ([(var) (unsafe-vector*-ref vec index)]) ;; inner bindings
                    #t ;; pre-guard
                    #t ;; post-guard
                    ((unsafe-fx+ 1 index) vec n))]))]
      [[(var ...) (in-gv gv-expr)]
       (with-syntax ([gv-expr-c (wrap-expr/c #'gvector? #'gv-expr #:macro #'in-gv)])
         (syntax/loc stx
           [(var ...) (in-gvector gv-expr-c)]))]
      [_ #f])))

(define-syntax (for/gvector stx)
  (syntax-case stx ()
    [(_ (clause ...) . body)
     #'(for/gvector #:capacity DEFAULT-CAPACITY (clause ...) . body)]
    [(_ #:capacity cap (clause ...) . body)
     (with-syntax ([((pre-body ...) post-body) (split-for-body stx #'body)])
       (quasisyntax/loc stx
         (let ([gv (make-gvector #:capacity cap)])
           (for/fold/derived #,stx () (clause ...)
            pre-body ...
	     (call-with-values (lambda () . post-body)
			       (case-lambda
				 [(one) (unsafe-gvector-add! gv one)]
				 [args (apply gvector-add! gv args)]))
	     (values))
           gv)))]))

(define-syntax (for*/gvector stx)
  (syntax-case stx ()
    [(_ (clause ...) . body)
     #'(for/gvector #:capacity DEFAULT-CAPACITY (clause ...) . body)]
    [(_ #:capacity cap (clause ...) . body)
     (with-syntax ([((pre-body ...) post-body) (split-for-body stx #'body)])
       (quasisyntax/loc stx
         (let ([gv (make-gvector #:capacity cap)])
           (for*/fold/derived #,stx () (clause ...)
            pre-body ...
            (call-with-values (lambda () . post-body)
                              (case-lambda
                                [(one) (begin (unsafe-gvector-add! gv one) (values))]
                                [args (begin (apply gvector-add! gv args) (values))])))
           gv)))]))

(provide
 gvector?
 (rename-out [gvector* gvector])
 make-gvector
 gvector-ref
 gvector-set!
 gvector-add!
 gvector-insert!
 gvector-remove!
 gvector-remove-last!
 gvector-append
 gvector-append!
 gvector-count
 gvector->vector
 gvector->list
 vector->gvector
 list->gvector
 (rename-out [in-gvector* in-gvector])
 for/gvector
 for*/gvector)

(module+ deserialize
  (provide deserialize-gvector)
  (define deserialize-gvector
    (make-deserialize-info
     (λ (vec)
       (vector->gvector vec))
     (λ ()
       (define gvec (make-gvector))
       (values
        gvec
        (λ (other)
          (for ([i (in-gvector other)])
            (gvector-add! gvec i))))))))
