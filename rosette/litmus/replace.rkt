#lang s-exp rosette

(require "../fs.rkt" "../lang.rkt" "../litmus.rkt" "../advfs.rkt" "../seqfs.rkt" "../verifier.rkt"
         rackunit rackunit/text-ui)

(provide replace-tests)

(define replace-setup
  (list (creat 0)  ; fd 0
        (write 0 '(#t))
        (fsync 0)))

(define replace-test-incorrect
  (list (creat 1)  ; fd 0
        (write 0 '(#t #t))
        ; (fsync 0)
        (rename 1 0)))
(define replace-test-correct
  (list (creat 1)  ; fd 0
        (write 0 '(#t #t))
        (fsync 0)
        (rename 1 0)))

; SeqFS
(define (replace-allow oldfs newfs)
  (define new-0 (ondisk newfs 0))
  (list (equal? new-0 '(#t))
        (equal? new-0 '(#t #t))))
(define (replace-fs-seqfs)
  (seq-fs 2))

; AdvFS
(define (replace-fs-advfs)
  (adv-fs 2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (test-seqfs-incorrect)
  (define test
    (litmus replace-fs-seqfs replace-setup replace-test-incorrect replace-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4))

(define (test-seqfs-correct)
  (define test
    (litmus replace-fs-seqfs replace-setup replace-test-correct replace-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4))

(define (test-advfs-incorrect)
  (define test
    (litmus replace-fs-advfs replace-setup replace-test-incorrect replace-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (sat? cex))
  (check-false (equal? (ondisk state 0) '(#t #t)))
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 3))  ; only 3 states: the write to 1 can never be synced

(define (test-advfs-correct)
  (clear-asserts!)
  (define test
    (litmus replace-fs-advfs replace-setup replace-test-correct replace-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4))

(define replace-tests
  (test-suite
   "replace litmus test"
   #:before (thunk (printf "-----replace-----\n"))
   (test-seqfs-incorrect)
   (test-seqfs-correct)
   (test-advfs-incorrect)
   (test-advfs-correct)
   ))

(time (run-tests replace-tests))
