#lang s-exp rosette

(require "../fs.rkt" "../lang.rkt" "../litmus.rkt" "../advfs.rkt" "../seqfs.rkt" "../verifier.rkt"
         rackunit rackunit/text-ui)

(provide two-appends-tests)

(define two-appends-setup '())

(define two-appends-test-incorrect
  (list
   (creat 0)
   (creat 1)
   (write 0 '(#t #t))
   ; (fsync 0)
   (write 1 '(#t))
   (fsync 1)))

(define two-appends-test-correct
  (list
   (creat 0)
   (creat 1)
   (write 0 '(#t #t))
   (fsync 0)
   (write 1 '(#t))
   (fsync 1)))

; SeqFS
(define (two-appends-allow oldfs newfs)
  (define new-0 (ondisk newfs 0))
  (define new-1 (ondisk newfs 1))
  (list (and (equal? new-0 #f)  (equal? new-1 #f))
        (and (equal? new-0 '()) (equal? new-1 #f))
        (and (equal? new-0 '()) (equal? new-1 '()))
        (and (equal? new-0 '(#t #t)) (equal? new-1 '()))
        (and (equal? new-0 '(#t #t)) (equal? new-1 '(#t)))))
(define (two-appends-fs-seqfs)
  (seq-fs 2))

; AdvFS
(define (two-appends-fs-advfs)
  (adv-fs 2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (test-seqfs-incorrect)
  (define test
    (litmus two-appends-fs-seqfs two-appends-setup two-appends-test-incorrect two-appends-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 5))

(define (test-seqfs-correct)
  (define test
    (litmus two-appends-fs-seqfs two-appends-setup two-appends-test-correct two-appends-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 5))

(define (test-advfs-incorrect)
  (define test
    (litmus two-appends-fs-advfs two-appends-setup two-appends-test-incorrect two-appends-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (sat? cex))
  (check-false (equal? (ondisk state 0) '(#t #t)))
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4))  ; only 4 states: the write to 0 can never be synced

(define (test-advfs-correct)
  (clear-asserts!)
  (define test
    (litmus two-appends-fs-advfs two-appends-setup two-appends-test-correct two-appends-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 5))

(define two-appends-tests
  (test-suite
   "two-appends litmus test"
   #:before (thunk (printf "-----two-appends-----\n"))
   (test-seqfs-incorrect)
   (test-seqfs-correct)
   (test-advfs-incorrect)
   (test-advfs-correct)
   ))

(time (run-tests two-appends-tests))
