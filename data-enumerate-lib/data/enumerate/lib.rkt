#lang racket/base
(require racket/contract
         racket/function
         racket/generator
         racket/bool
         racket/match
         (only-in racket/list remove-duplicates partition)
         syntax/location
         math/base
         math/distributions
         math/number-theory
         math/flonum
         "../enumerate.rkt"
         (prefix-in unsafe: "unsafe.rkt")
         (for-syntax racket/base))
(provide (all-from-out "../enumerate.rkt"))

;; random-natural-w/o-limit : ([0,1] -> Nat) ∩ (-> Nat)
(define (random-natural-w/o-limit [prob-of-zero 0.01])
  (max (random-natural/no-mean prob-of-zero)
       (random-natural/no-mean prob-of-zero)
       (random-natural/no-mean prob-of-zero)))

;; random-natural/no-mean : [0,1] -> Nat
(define (random-natural/no-mean prob-of-zero)
  (define x (sample (geometric-dist prob-of-zero)))
  (define m1 (expt 2 (exact-floor x)))
  (define m0 (quotient m1 2))
  (random-integer m0 m1))

(define (random-index e)
  (if (infinite-enum? e)
      (random-natural-w/o-limit)
      (random-natural (enum-size e))))

(define (BPP-digits N)
  (let loop ([8Pi -8])
    (define 8i
      (+ 8 8Pi))

    (define (E k)
      (/ 1 (+ 8i k)))

    (define pi_i
      (* N
         (+ (* +4 (E 1))
            (* -2 (E 4))
            (* -1 (E 5))
            (* -1 (E 6)))))

    (for ([c (in-string (number->string pi_i))])
      (unless (eq? #\/ c)
        (yield (- (char->integer c) (char->integer #\0)))))

    (loop 8i)))

;; exported to tests/data/enumerate
(module+ test (provide BPP-digits 10-sequence->K-sequence))

(define (bits-of k)
  (/ (log k) (log 2)))

;; XXX just subtract k if greater than k and then push the digit to
;; left and go on
(define (10-sequence->K-sequence k seq)
  (cond
   [(< k 10)
    (10-sequence->sub10-sequence k seq)]
   [(= k 10)
    seq]
   [else
    (10-sequence->sup10-sequence k seq)]))

(define (10-sequence->sub10-sequence k seq)
  (in-generator
   (for ([d seq])
     (when (< d k)
       (yield d)))))

(define (10-sequence->sup10-sequence k seq)
  (in-generator
   (let loop ()
     (define d
       (for/sum ([i (in-range (ceiling (/ (log k) (log 10))))]
                 [sub-d seq])
         (* sub-d (expt 10 i))))
     (yield (modulo d k))
     (loop))))

(define (infinite-sequence/e inner/e)
  (define seed/e nat/e)
  (define K (enum-size inner/e))
  (define (seed->seq N)
    (define K-seq
      (10-sequence->K-sequence K (in-generator (BPP-digits (+ 1 N)))))
    (in-generator
     (for ([k K-seq])
       (yield (from-nat inner/e k)))))
  (pam/e seed->seq seed/e #:contract sequence?))

(provide cons/de)
(define-syntax (cons/de stx)
  (define dep-expression-finite #f)
  (define (parse-options options)
    (let loop ([options options])
      (syntax-case options ()
        [() (void)]
        [(#:dep-expression-finite? exp . options)
         (begin
           (when dep-expression-finite
             (raise-syntax-error 'cons/de "expected only one use of #:dep-expression-finite?"
                                 stx
                                 dep-expression-finite
                                 (list #'exp)))
           (set! dep-expression-finite #'exp)
           (loop #'options))]
        [(x . y)
         (raise-syntax-error 'cons/de "bad syntax" stx #'x)])))
  (define the-srcloc
    #`(srcloc '#,(syntax-source stx)
              #,(syntax-line stx)
              #,(syntax-column stx)
              #,(syntax-position stx)
              #,(syntax-span stx)))
  (define other-party-name (syntax-local-lift-expression #'(quote-module-name)))
  (syntax-case stx ()
    [(_ [hd e1] [tl (hd2) e2] . options)
     (begin
       (unless (free-identifier=? #'hd #'hd2)
         (raise-syntax-error 'cons/de "expected the identifiers to be the same"
                             stx
                             #'hd
                             (list #'hd2)))
       (parse-options #'options)
       #`(cons/de/proc e1 (λ (hd2) e2) #,dep-expression-finite #f 
                       #,the-srcloc #,other-party-name))]
    [(_ [hd (tl2) e1] [tl e2] . options)
     (begin
       (unless (free-identifier=? #'tl #'tl2)
         (raise-syntax-error 'cons/de "expected the identifiers to be the same"
                             stx
                             #'tl
                             (list #'tl2)))
       (parse-options #'options)
       #`(cons/de/proc e2 (λ (tl2) e1) #,dep-expression-finite #t 
                       #,the-srcloc #,other-party-name))]))
                       
(define (cons/de/proc e _f f-range-finite? flip? the-srcloc other-party-name)
  (define f-range-ctc
    (and/c (if f-range-finite?
               finite-enum?
               infinite-enum?)
           (if (two-way-enum? e)
               two-way-enum?
               one-way-enum?)))
  (define (f v)
    (contract f-range-ctc
              (_f v) 
              other-party-name 
              'data/enumerate 
              'cons/de/dependent-expression
              the-srcloc))
  (define forward (unsafe:dep/e-internal e f f-range-finite?))
  (if flip?
      (flip-it forward e f)
      forward))

(provide
 (contract-out
  [flip-dep/e unsafe:dep/e-contract]))
(define (flip-dep/e e f #:f-range-finite? [f-range-finite? #f])
  (flip-it (unsafe:dep/e-internal e f f-range-finite?) e f))
(define (flip-it to-flip e f)
  (define (flip-pr ab) (cons (cdr ab) (car ab)))
  (map/e
   flip-pr flip-pr 
   to-flip
   #:contract
   (cons/dc [hd (tl) (enum-contract (f tl))] [tl (enum-contract e)])))

(define (permutations-of-n/e n)
  (cond
    [(zero? n)
     (fin/e '())]
    [else
     (define p-sub1 (permutations-of-n/e (sub1 n)))
     (define elem/c (integer-in 0 (- n 1)))
     (map/e
      values
      values
      (cons/de
       [v (below/e n)]
       [tl (v)
           (unsafe:map/e
            (λ (l)
              (for/list ([i (in-list l)])
                (if (< i v)
                    i
                    (+ i 1))))
            (λ (l)
              (for/list ([i (in-list l)])
                (if (< i v)
                    i
                    (- i 1))))
            p-sub1
            #:contract
            any/c)]
       #:dep-expression-finite? #t)
      #:contract
      (and/c (apply list/c (build-list n (λ (_) elem/c)))
             no-duplicates?))]))

(define (no-duplicates? l) 
  (= (length (remove-duplicates l)) 
     (length l)))

(define (permutations/e l #:contract [c 
                                      (if (andmap contract? l)
                                          (apply or/c l)
                                          (error 'permutations/e
                                                 "expected an explicit contract"))])
  (define idx->e (list->vector l))
  (define e->idx
    (for/hash ([e (in-list l)]
               [i (in-naturals)])
      (values e i)))
  (map/e
   (λ (l)
     (for/list ([idx (in-list l)])
       (vector-ref idx->e idx)))
   (λ (l)
     (for/list ([e (in-list l)])
       (hash-ref e->idx e)))
   (permutations-of-n/e (vector-length idx->e))
   #:contract (and/c (apply list/c (build-list (length l) (λ (_) c)))
                     no-duplicates?)))

(provide
 (contract-out
  [random-index
   (-> enum? exact-nonnegative-integer?)]
  [infinite-sequence/e
   (-> enum? enum?)]
  [permutations/e
   (-> list? enum?)]
  [permutations-of-n/e
   (-> exact-nonnegative-integer? enum?)]))

(provide
 (contract-out
  [range/e
   (->i ([low (or/c exact-integer? -inf.0)]
         [high (or/c exact-integer? +inf.0)])
        #:pre (low high) (<= low high)
        [res enum?])]))

(define (range/e low high)
  (cond 
    [(and (infinite? high) (infinite? low))
     integer/e]
    [(infinite? high)
     (map/e
      (λ (n)
        (+ n low))
      (λ (n)
        (- n low))
      nat/e
      #:contract (and/c exact-integer? (>=/c low)))]
    [(infinite? low)
     (map/e
      (λ (n) (- high n))
      (λ (n) (- high n))
      nat/e
      #:contract (and/c exact-integer? (<=/c high)))]
    [else
     (map/e (λ (n) (+ n low))
            (λ (n) (- n low))
            (below/e (+ 1 (- high low)))
            #:contract (and/c (between/c low high)
                              exact-integer?))]))

(provide
 (contract-out
  [nat+/e (-> exact-nonnegative-integer? enum?)]))
(define (nat+/e n)
  (map/e (λ (k) (+ k n))
         (λ (k) (- k n))
         nat/e
         #:contract
         (and/c (>=/c n) exact-integer?)))



(provide
 (contract-out
  [fold-enum
   (->i ([f (f-range-finite?)
            (if (or (unsupplied-arg? f-range-finite?)
                    (not f-range-finite?))
                (-> list? any/c infinite-enum?)
                (-> list? any/c finite-enum?))]
         [l list?])
        (#:f-range-finite? [f-range-finite? boolean?])
        [result enum?])]))

;; fold-enum : ((listof a), b -> enum a), (listof b) -> enum (listof a)
(define (fold-enum f l #:f-range-finite? [f-range-finite? #f])
  (define e
    (let loop ([l l]
               [acc (fin/e '())])
      (cond [(null? l) acc]
            [else
             (loop
              (cdr l)
              (cons/de [hd (xs) (f xs (car l))]
                       [xs acc]
                       #:dep-expression-finite? f-range-finite?))])))
  (map/e
   reverse
   reverse
   e
   #:contract (reverse/c (enum-contract e))))

(define (reverse/c ctc)
  ((cond
     [(chaperone-contract? ctc)
      make-chaperone-contract]
     [else
      make-contract])
   #:name `(reverse/c ,(contract-name ctc))
   #:first-order list?
   #:projection
   (let ([proj (contract-projection ctc)])
     (λ (b)
       (define proj+b (proj b))
       (λ (v)
         (if (list? v)
             (reverse (proj+b (reverse v)))
             (proj+b v)))))
   #:stronger (λ (this that) #f)
   #:list-contract? #t))

(define listof/e-contract
  (->i ([e (simple-recursive?) 
           (if (or (unsupplied-arg? simple-recursive?)
                   simple-recursive?)
               enum?
               infinite-enum?)])
       (#:simple-recursive? [simple-recursive? any/c])
       [res enum?]))
(provide
 (contract-out
  [listof/e listof/e-contract]
  [non-empty-listof/e listof/e-contract]))

(define (listof/e e #:simple-recursive? [simple-recursive? #t])
  (cond
    [simple-recursive?
     (define fix-size
       (if (and (finite-enum? e) (= 0 (enum-size e)))
           1
           +inf.0))
     (define result-e
       (delay/e
        (or/e (cons (fin/e '()) null?)
              (cons (cons/e e result-e) pair?))
        #:size fix-size
        #:two-way-enum? (two-way-enum? e)
        #:flat-enum? (flat-enum? e)))
     (map/e values values result-e #:contract (listof (enum-contract e)))]
    [else
     (or/e
      (fin/e '())
      (non-empty-listof/e e #:simple-recursive? #f))]))

(define (non-empty-listof/e e #:simple-recursive? [simple-recursive? #t])
  (cond
    [simple-recursive? 
     (except/e (listof/e e #:simple-recursive? #t) '()
               #:contract (non-empty-listof (enum-contract e)))]
    [else 
     (map/e 
      cdr 
      (λ (x) (cons (- (length x) 1) x))
      (cons/de
       [i nat/e]
       [tl (i) (apply list/e (build-list (+ i 1) (λ (_) e)))])
      #:contract (non-empty-listof (enum-contract e)))]))

(provide
 (contract-out
  [listof-n/e (-> enum? exact-nonnegative-integer? enum?)]))
(define (listof-n/e e n)
  (apply list/e (build-list n (const e))))

(provide
 (contract-out
  [take/e
   (->i ([e enum?] 
         [s (e) 
            (if (finite-enum? e)
                (integer-in 0 (- (enum-size e) 1))
                exact-nonnegative-integer?)])
        (#:contract [c contract?])
        #:pre (c e)
        (implies (unsupplied-arg? c)
                 (and (two-way-enum? e)
                      (flat-contract? (enum-contract e))))
        [result enum?])]))
(define (take/e e n #:contract [contract 
                                (λ (x)
                                  (and ((enum-contract e) x)
                                       (< (to-nat e x) n)))])
  (slice/e e 0 n))

(provide
 (contract-out
  [slice/e
   (->i ([e enum?] [lo exact-nonnegative-integer?] [hi exact-nonnegative-integer?])
        (#:contract [c contract?])
        #:pre (lo hi) (<= lo hi)
        #:pre (e hi) (or (infinite-enum? e) (hi . <= . (enum-size e)))
        #:pre (c e)
        (implies (unsupplied-arg? c)
                 (and (two-way-enum? e)
                      (flat-contract? (enum-contract e))))
        [res enum?])]))
(define (slice/e e lo hi 
                 #:contract 
                 [contract 
                  (and/c (enum-contract e)
                         (let ([in-the-slice?
                                (λ (x)
                                  (define n (to-nat e x))
                                  (and (<= lo n)
                                       (< n hi)))])
                           in-the-slice?))])
  (map/e
   (λ (n) (from-nat e (n . + . lo)))
   (λ (x) (- (to-nat e x) lo))
   (below/e (hi . - . lo))
   #:contract contract))

(provide
 (contract-out
  [hash-traverse/e
   (-> (-> any/c enum?) 
       hash?
       #:get-contract (-> any/c contract?)
       enum?)]))

;; Hash Traversal
;; hash-traverse/e : (a -> enum b), (hash[k] -o> a) -> enum (hash[k] -o> b)
#;
(define (hash-traverse/e f ht)
  ;; as-list : listof (cons k a)
  (define as-list (hash->list ht))
  ;; on-cdr : (cons k a) -> enum (cons k b)
  
  (define/match (on-cdr pr)
    [((cons k v))
     (map/e (λ (x) (cons k x))
            cdr
            (f v)
            #:contract any/c)])
  ;; enum (listof (cons k b))
  (define assoc/e
    (apply list/e (map on-cdr as-list)))
  (define (hash-that-maps-correct-keys? candidate-ht)
    (define b (box #f))
    (for/and ([k (in-hash-keys ht)])
      (not (eq? (hash-ref candidate-ht k b) b))))
  (map/e make-immutable-hash
         hash->list
         assoc/e
         #:contract 
         (and/c
          hash?
          hash-that-maps-correct-keys?
          (hash/dc [k any/c]
                   [v (k) (enum-contract (f k))]))))

;; Hash Traversal
;; hash-traverse/e : (a -> enum b), (hash[k] -o> a) -> enum (hash[k] -o> b)
(define (hash-traverse/e f ht #:get-contract get-contract)
  ;; as-list : listof (cons k a)
  (define as-list (hash->list ht))
  ;; on-cdr : (cons k a) -> enum (cons k b)
  (define/match (on-cdr pr)
    [((cons k v))
     (map/e (λ (x) (cons k x))
            cdr
            (f v)
            #:contract any/c)])
  ;; enum (listof (cons k b))
  (define assoc/e
    (apply list/e (map on-cdr as-list)))
  (define (hash-that-maps-correct-keys? x) #t)
  (map/e make-immutable-hash
         hash->list
         assoc/e
         #:contract (and/c
                     hash?
                     hash-that-maps-correct-keys?
                     (hash/dc [k any/c]
                              [v (k) (get-contract k)]))))


(provide
 (contract-out
  [cons/e
   (->* (enum? enum?)
        (#:ordering (or/c 'diagonal 'square))
        enum?)]))
;; cons/e : enum a, enum b ... -> enum (cons a b ...)
(define (cons/e e1 e2 #:ordering [ordering 'square])
  (map/e (λ (x) (cons (car x) (cadr x)))
         (λ (x-y) (list (car x-y) (cdr x-y)))
         (list/e e1 e2 #:ordering ordering)
         #:contract (cons/c (enum-contract e1) (enum-contract e2))))

(provide delay/e)
(define-syntax (delay/e stx)
  (syntax-case stx ()
    [(_ expr . kwd-args)
     (let ()
       (when (keyword? (syntax-e #'expr))
         (raise-syntax-error 'delay/e 
                             "expected an expression argument first, not a keyword"
                             stx #'expr))
       (define other-party-name (syntax-local-lift-expression #'(quote-module-name)))
       (define the-srcloc
         #`(srcloc '#,(syntax-source stx)
                   #,(syntax-line stx)
                   #,(syntax-column stx)
                   #,(syntax-position stx)
                   #,(syntax-span stx)))
       #`((delay/e/proc #,other-party-name #,the-srcloc (λ () expr)) . kwd-args))]))

(define (delay/e/proc other-party-name the-srcloc thunk)
  ;; do this curried thing to get better error reporting for keyword arity errors
  (define (delay/e #:size [size +inf.0]
                   #:two-way-enum? [is-two-way-enum? #t]
                   #:flat-enum? [is-flat-enum? #t])
    
    (define ctc
      (and/c (if (= size +inf.0)
                 infinite-enum?
                 (and/c finite-enum?
                        (let ([matching-size? (λ (e) (= (enum-size e) size))])
                          matching-size?)))
             (if is-two-way-enum?
                 two-way-enum?
                 one-way-enum?)
             (if is-flat-enum?
                 flat-enum?
                 (not/c flat-enum?))))
    (unless (or (exact-nonnegative-integer? size)
                (and (number? size) (= size +inf.0)))
      (raise-argument-error 'delay/e 
                            (format "~s" '(or/c exact-nonnegative-integer? +inf.0))
                            size))
    (thunk/e (λ () (contract ctc
                             (thunk)
                             other-party-name 
                             'data/enumerate/lib 
                             'delay/e-expression
                             the-srcloc))
              #:size size
              #:two-way-enum? is-two-way-enum?
              #:flat-enum? is-flat-enum?))
  delay/e)

(provide
 (contract-out
  [fin/e
   (->i ()
        #:rest
        [elements 
         (listof (or/c symbol? boolean? char? keyword? null?
                       string? bytes? number?))]
        #:pre/name (elements) 
        "no duplicate elements"
        (let ()
          (define-values (nums non-nums) (partition number? elements))
          (and (= (length (remove-duplicates nums =))
                  (length nums))
               (= (length (remove-duplicates non-nums))
                  (length non-nums))))
        [result enum?])]))
(define (fin/e . args)
  (cond
    [(null? args) empty/e]
    [else
     (define (use-=? x) (and (number? x) (not (memv x '(+nan.0 +nan.f)))))
     (define-values (use-= use-equal?) (partition use-=? args))
     (define rev-map (make-hash))
     (define num-rev-map (list))
     (for ([i (in-naturals)]
           [x (in-list args)])
       (cond
         [(use-=? x)
          (set! num-rev-map (cons (cons x i) num-rev-map))]
         [else
          (hash-set! rev-map x i)]))
     (set! num-rev-map (reverse num-rev-map))
     (define vec (list->vector args))
     (map/e (λ (n) (vector-ref vec n))
            (λ (x) 
              (cond
                [(use-=? x)
                 (for/first ([pr (in-list num-rev-map)]
                             #:when (= x (car pr)))
                   (cdr pr))]
                [else (hash-ref rev-map x)]))
            (below/e (vector-length vec))
            #:contract (apply or/c args))]))



;; Base Type enumerators

(provide
 char/e
 string/e
 integer/e
 flonum/e
 exact-rational/e
 real/e
 two-way-real/e
 number/e
 two-way-number/e
 bool/e
 symbol/e)

(define (between? x low high)
  (and (>= x low)
       (<= x high)))
(define (range-with-pred/e-p low high)
  (cons (range/e low high)
        (λ (n) (between? n low high))))
(define low/e-p
  (range-with-pred/e-p #x61 #x7a))
(define up/e-p
  (range-with-pred/e-p #x41 #x5a))
(define bottom/e-p
  (range-with-pred/e-p #x0 #x40))
(define mid/e-p
  (range-with-pred/e-p #x5b #x60))
(define above1/e-p
  (range-with-pred/e-p #x7b #xd7FF))
(define above2/e-p
  (range-with-pred/e-p #xe000 #x10ffff))

(define char/e
  (map/e
   integer->char
   char->integer
   (append/e low/e-p
             up/e-p
             bottom/e-p
             mid/e-p
             above1/e-p
             above2/e-p)
   #:contract char?))

(define better-ordering-for-sequences-of-chars/e
  (append/e (list/e char/e)
            (fin/e '())
            (cons/e char/e (cons/e char/e (listof/e char/e)))))

(define string/e
  (map/e
   list->string
   string->list
   better-ordering-for-sequences-of-chars/e
   #:contract string?))

(define integer/e
  (let ()
    (define (i-from-nat x)
      (cond
        [(even? x) (- (/ x 2))]
        [else (/ (+ x 1) 2)]))
    (define (i-to-nat x)
      (cond
        [(<= x 0) (* (- x) 2)]
        [else (- (* x 2) 1)]))
    (map/e i-from-nat
           i-to-nat
           nat/e
           #:contract exact-integer?)))

(define normal-flonums/e-p
  (take/e (map/e
           ordinal->flonum
           flonum->ordinal
           integer/e
           #:contract flonum?)
          (+ 1 (* 2 9218868437227405311))
          #:contract 
          (and/c flonum?
                 (not/c infinite?)
                 (not/c nan?))))

(define flonum/e
  (append/e (fin/e +inf.0 -inf.0 +nan.0)
            normal-flonums/e-p))

(define exact-rational/e
  (or/e (fin/e 0)
        (let ([pos-exact-rational/e
               (pam/e (λ (pr) (/ (car pr) (cdr pr)))
                      (cons/e (nat+/e 1) (nat+/e 2))
                      #:contract (and/c rational? positive?))])
          (or/e pos-exact-rational/e
                (pam/e - pos-exact-rational/e
                       #:contract (and/c rational? exact? negative?))))))
         
(define two-way-real/e (or/e integer/e flonum/e))
(define real/e (or/e flonum/e exact-rational/e))

(define (make-non-real/e rp ip ctc)
  (map/e make-rectangular
         (λ (z)
           (values (real-part z)
                   (imag-part z)))
         rp ip
         #:contract ctc))

(define (complex-with-exact-integer-parts? x)
  (and (number? x)
       (exact-integer? (real-part x))
       (exact-integer? (imag-part x))))
(define exact-integer-non-real/e
  (make-non-real/e (except/e integer/e 0) (except/e integer/e 0)
                   (and/c complex-with-exact-integer-parts? (not/c real?))))
(define float-non-real/e 
  (make-non-real/e flonum/e flonum/e
                   (and/c number? inexact? (not/c real?))))

;; only one-way, so don't need to skip 0
(define exact-rational-complex/e 
  (make-non-real/e exact-rational/e exact-rational/e
                   (and/c number? exact?)))

(define number/e
   (or/e real/e
         float-non-real/e
         exact-rational-complex/e))
(define (complex-with-exact-zero-real-part? x)
  (and (number? x)
       (equal? 0 (real-part x))))

(define two-way-number/e
  (or/e two-way-real/e
        (map/e (λ (x) (make-rectangular 0 x)) 
               imag-part
               two-way-real/e 
               #:contract complex-with-exact-zero-real-part?)
        exact-integer-non-real/e
        float-non-real/e))

(define bool/e (fin/e #t #f))

(define symbol/e
  (map/e
   (compose string->symbol list->string)
   (compose string->list symbol->string)
   better-ordering-for-sequences-of-chars/e
   #:contract symbol?))

(provide
 (contract-out
  [vector/e
   (->* ()
        (#:ordering (or/c 'diagonal 'square)) 
        #:rest (listof enum?)
        enum?)]))

(define (vector/e #:ordering [ordering 'square] . es)
  (map/e list->vector
         vector->list
         (apply list/e #:ordering ordering es)
         #:contract (apply vector/c (map enum-contract es))))


(provide
 (contract-out
  [single/e
   (->* (any/c)
        (#:equal? (-> any/c any/c boolean?))
        finite-enum?)]))
(define (single/e v #:equal? [same? equal?])
  (define (single/e-contract a) (same? v a))
  (map/e (λ (_) v)
         (λ (_) 0)
         (below/e 1)
         #:contract single/e-contract))