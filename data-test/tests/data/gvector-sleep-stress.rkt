#lang racket/base
;; Stress tests that recompile data/gvector with GVECTOR_SLEEP set to
;; widen specific race windows. Each test activates only the sleep
;; point relevant to the invariant it tests, so other operations
;; remain fast. The gvector module is loaded via dynamic-require with
;; compiled file loading disabled, so the sleep-enabled version is
;; never cached.

(require rackunit
         racket/unsafe/ops)

(define (make-gvector-ns tag)
  ;; Set GVECTOR_SLEEP to the tag so only the matching maybe-sleep
  ;; expands to (sleep 0.01). Load in a fresh namespace with compiled
  ;; files disabled. Returns a lookup function for that namespace.
  (putenv "GVECTOR_SLEEP" tag)
  (define ns (make-base-namespace))
  (parameterize ([use-compiled-file-paths '()]
		 [current-namespace ns])
    (dynamic-require 'data/gvector #f))
  (putenv "GVECTOR_SLEEP" "")
  (lambda (sym)
    (parameterize ([use-compiled-file-paths '()]
		   [current-namespace ns])
      (dynamic-require 'data/gvector sym))))

(define ref-ns (make-gvector-ns "ref"))
(define trim-ns (make-gvector-ns "trim"))
(define es-ns (make-gvector-ns "ensure-space"))

;; Test 1: vec-before-n ordering in gvector-ref.
;; Only gvector-ref sleeps (tag "ref"); removes run at full speed.
;; A reader reads vec, sleeps 10ms, then reads n. During the sleep,
;; many concurrent removes can decrement n and trigger trim! which
;; replaces vec with a shorter one. With correct vec-before-n ordering,
;; the reader holds the old (large) vec and reads the new (small) n —
;; safe. With wrong n-before-vec ordering, the reader reads the old
;; (large) n and the new (small) vec — out of bounds.
(test-case "sleep-stress: ref + remove (vec-before-n ordering)"
  (define make-gvector* (ref-ns 'make-gvector))
  (define gvector-add!* (ref-ns 'gvector-add!))
  (define gvector-ref* (ref-ns 'gvector-ref))
  (define gvector-count* (ref-ns 'gvector-count))
  (define gvector-remove-last!* (ref-ns 'gvector-remove-last!))
  (for ([iter (in-range 5)])
    (define gv (make-gvector*))
    ;; Fill with enough elements that removing triggers trim!
    ;; trim! fires when cap >= 4*n, so starting at n=1000 with
    ;; cap=1024, after 744 removes n=256 and cap=1024 >= 4*256,
    ;; so trim! shrinks to 512. Further removes trigger more shrinks.
    (for ([i 1000])
      (gvector-add!* gv i))
    (define pool (make-parallel-thread-pool 4))
    (define stop? #f)
    (define found-garbage? #f)
    ;; Readers that access near the end of the gvector.
    ;; Each ref takes ~10ms due to the sleep.
    ;; Check that returned values are valid (fixnums 0-999 or #f).
    (define readers
      (for/list ([t (in-range 2)])
        (thread #:pool pool
                (lambda ()
                  (let loop ()
                    (define n (gvector-count* gv))
                    (when (> n 0)
                      (define val (gvector-ref* gv (sub1 n) #f))
                      (when (and val (not (and (fixnum? val) (<= 0 val 999))))
                        (set! found-garbage? #t)))
                    (unless stop?
                      (loop)))))))
    ;; Removers run at full speed (no sleep in remove/trim)
    (define removers
      (for/list ([t (in-range 2)])
        (thread #:pool pool
                (lambda ()
                  (for ([_ (in-range 400)])
                    (with-handlers ([exn:fail? void])
                      (gvector-remove-last!* gv)))))))
    (for-each thread-wait removers)
    (set! stop? #t)
    (parallel-thread-pool-close pool)
    (for-each thread-wait readers)
    (check-false found-garbage?
                 (format "iter ~a: read garbage from beyond vector bounds" iter))))

;; Test 2: trim! under concurrent add pressure.
;; Only trim! sleeps (tag "trim"); adds run at full speed.
;; Exercises two protections in trim!:
;; (a) CAS on vec: if a grower installed a larger vec during the sleep,
;;     CAS fails and trim! retries rather than clobbering.
;; (b) n re-read: if concurrent adds grew n past the target capacity
;;     without changing vec (because it had room), trim! aborts.
;; The invariant violation (n > vector-length(vec)) is transient and
;; hard to observe because adds immediately re-grow, so the test
;; primarily verifies no crashes or memory errors occur.
(test-case "sleep-stress: add + remove (trim! CAS)"
  (define make-gvector* (trim-ns 'make-gvector))
  (define gvector-add!* (trim-ns 'gvector-add!))
  (define gvector-ref* (trim-ns 'gvector-ref))
  (define gvector-count* (trim-ns 'gvector-count))
  (define gvector-remove-last!* (trim-ns 'gvector-remove-last!))
  (for ([iter (in-range 5)])
    (define gv (make-gvector*))
    ;; Start with enough elements that removing triggers trim!
    ;; n=1000, cap=1024. After ~744 removes, cap >= 4*n triggers shrink.
    (for ([i 1000])
      (gvector-add!* gv i))
    (define pool (make-parallel-thread-pool 6))
    (define stop? #f)
    (define found-garbage? #f)
    ;; Writers add continuously so they're active during trim!'s sleep.
    ;; Each trim! sleeps 10ms; writers must be adding during that window
    ;; so they push n past trim!'s target capacity.
    (define writers
      (for/list ([t (in-range 2)])
        (thread #:pool pool
                (lambda ()
                  (let loop ()
                    (with-handlers ([exn:fail? void])
                      (gvector-add!* gv 42))
                    (unless stop?
                      (loop)))))))
    ;; Checkers continuously verify n <= vector-length(vec) directly.
    ;; gvector-ref can't detect this because vec-before-n ordering
    ;; makes it safe even when the invariant is transiently violated.
    ;; We read the struct fields directly via unsafe-struct*-ref
    ;; (vec=field 0, n=field 1) to observe the transient violation.
    (define readers
      (for/list ([t (in-range 2)])
        (thread #:pool pool
                (lambda ()
                  (let loop ()
                    ;; Read vec first, then n. If trim! just installed
                    ;; a small vec and n is still large from adds,
                    ;; we see v=small, n=large => violation.
                    (define v (unsafe-struct*-ref gv 0))
                    (define n (unsafe-struct*-ref gv 1))
                    (when (> n (vector-length v))
                      (set! found-garbage? #t))
                    (unless stop?
                      (loop)))))))
    ;; Removers trigger trim! which sleeps between reading vec and CAS
    (define removers
      (for/list ([t (in-range 2)])
        (thread #:pool pool
                (lambda ()
                  (for ([_ (in-range 400)])
                    (with-handlers ([exn:fail? void])
                      (gvector-remove-last!* gv)))))))
    (for-each thread-wait removers)
    (set! stop? #t)
    (for-each thread-wait writers)
    (for-each thread-wait readers)
    (parallel-thread-pool-close pool)
    (check-false found-garbage?
                 (format "iter ~a: read garbage from beyond vector bounds" iter))))

;; Test 3: CAS in define/ensure-space!.
;; Only ensure-space! sleeps (tag "ensure-space"); other ops fast.
;; Two growers both read the same vec, sleep 10ms, then both try to
;; create and install new vectors. With CAS, only one succeeds and
;; the other retries. Without CAS, both install and the last writer
;; wins — which may be the thread creating the smaller vec while the
;; other thread increments n past that vec's length.
;; Note: see comment at test about reliable detection.
(test-case "sleep-stress: concurrent add (ensure-space! CAS)"
  (define make-gvector* (es-ns 'make-gvector))
  (define gvector-add!* (es-ns 'gvector-add!))
  (define gvector-ref* (es-ns 'gvector-ref))
  (define gvector-count* (es-ns 'gvector-count))
  (for ([iter (in-range 5)])
    (define gv (make-gvector*))
    ;; Fill to capacity to force resize on next add
    (for ([i 10])
      (gvector-add!* gv i))
    (define pool (make-parallel-thread-pool 2))
    ;; Use symbols so we can distinguish from garbage memory
    (define sentinel (gensym 'val))
    (define t1 (thread #:pool pool (lambda () (gvector-add!* gv sentinel))))
    (define t2
      (thread #:pool pool
              (lambda () (apply gvector-add!* gv (build-list 100 (lambda (_) sentinel))))))
    (thread-wait t1)
    (thread-wait t2)
    (parallel-thread-pool-close pool)
    ;; Verify invariant by reading every element.
    ;; With a missing CAS, this may read garbage beyond the vector.
    ;; However, detection is not guaranteed since the thread creating
    ;; the larger vector tends to win the vec write.
    (define count (gvector-count* gv))
    (for ([i (in-range count)])
      (define val (gvector-ref* gv i))
      (check-true (or (fixnum? val) (eq? val sentinel))
                  (format "iter ~a: garbage at index ~a: ~v" iter i val)))))
