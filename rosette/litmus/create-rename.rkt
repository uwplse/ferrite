#lang s-exp rosette

(require "../fs.rkt" "../lang.rkt" "../litmus.rkt" "../verifier.rkt" "../synth.rkt"
         "../advfs.rkt" "../seqfs.rkt" "../ext4.rkt"
         rackunit rackunit/text-ui)

(provide create-rename-tests)

(current-bitwidth 16)

(define small? #f)
(define block-size (if small? 64 4096))

(define create-rename-setup '())

(define create-rename-test-incorrect
  (list
   (creat 0)
   (write 0 '(#t #t))
   ; (fsync 0)
   (rename 0 1)))

(define create-rename-test-correct
  (list
   (creat 0)
   (write 0 '(#t #t))
   (fsync 0)
   (rename 0 1)))


; SeqFS
(define (create-rename-allow oldfs newfs)
  (define new-1 (ondisk newfs 1))
  (list (equal? new-1 #f)
        (equal? new-1 '(#t #t))))
(define (create-rename-fs-seqfs)
  (seq-fs 2))

; AdvFS
(define (create-rename-fs-advfs)
  (adv-fs 2))

; Ext4
(define (create-rename-fs-ext4)
  (ext4-fs #:capacity 2 #:blocksize block-size))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (test-seqfs-incorrect)
  (define test
    (litmus create-rename-fs-seqfs create-rename-setup create-rename-test-incorrect create-rename-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4))

(define (test-seqfs-correct)
  (define test
    (litmus create-rename-fs-seqfs create-rename-setup create-rename-test-correct create-rename-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4))

(define (test-advfs-incorrect)
  (define test
    (litmus create-rename-fs-advfs create-rename-setup create-rename-test-incorrect create-rename-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (sat? cex))
  (check-true (equal? (ondisk state 1) '()))
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 3))  ; only 3 states: the write can never be synced

(define (test-advfs-correct)
  (clear-state!)
  (define test
    (litmus create-rename-fs-advfs create-rename-setup create-rename-test-correct create-rename-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4))

(define (test-ext4-incorrect)
  (define test
    (litmus create-rename-fs-ext4 create-rename-setup create-rename-test-incorrect create-rename-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (sat? cex)) ; rename can be reordered before sync
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 5))

(define (test-ext4-correct)
  (define test
    (litmus create-rename-fs-ext4 create-rename-setup create-rename-test-correct create-rename-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4))

(define (test-advfs-synth)
  (define test
    (litmus create-rename-fs-advfs create-rename-setup create-rename-test-incorrect create-rename-allow))
  (define prog (synth test))
  (check-false (false? prog))
  (check-false (term? prog))
  (printf "create-rename advfs:\n  before:  ~v\n  after: ~v\n"
          create-rename-test-incorrect
          (remove-disabled-syncs prog))
  (define cost (sync-cost prog))
  (check equal? cost 1)
  (define test*
    (litmus create-rename-fs-advfs create-rename-setup prog create-rename-allow))
  (define-values (cex state) (verify-correctness test*))
  (check-true (unsat? cex)))

(define (test-ext4-synth)
  (define test
    (litmus create-rename-fs-ext4 create-rename-setup create-rename-test-incorrect create-rename-allow))
  (define prog (synth test))
  (check-false (false? prog))
  (check-false (term? prog))
  (printf "create-rename ext4:\n  before:  ~v\n  after: ~v\n"
          create-rename-test-incorrect
          (remove-disabled-syncs prog))
  (define cost (sync-cost prog))
  (check equal? cost 1)
  (define test*
    (litmus create-rename-fs-ext4 create-rename-setup prog create-rename-allow))
  (define-values (cex state) (verify-correctness test*))
  (check-true (unsat? cex)))


(define create-rename-tests
  (test-suite
   "create-rename litmus test"
   #:before (thunk (printf "-----create-rename-----\n"))
   (test-seqfs-incorrect)
   (test-seqfs-correct)
   (test-advfs-incorrect)
   (test-advfs-correct)
   (test-ext4-incorrect)
   (test-ext4-correct)
   ))

(define create-rename-synth-tests
  (test-suite
   "create-rename synth test"
   #:before (thunk (printf "-----create-rename synth-----\n"))
   (test-advfs-synth)
   (test-ext4-synth)
   ))
   
(time (run-tests create-rename-tests))  ; small? = #f: passes in 9s
(time (run-tests create-rename-synth-tests))  ; small? = #f: passes in 30s
