#lang s-exp rosette

(require "../fs.rkt" "../lang.rkt" "../litmus.rkt" "../verifier.rkt" "../synth.rkt"
         "../advfs.rkt" "../seqfs.rkt" "../ext4.rkt" 
         rackunit rackunit/text-ui)

(provide chrome-tests)

(current-bitwidth 16)

(define small? #f)
(define writes (if small? '(33 2 31) '(2509 13 2500)))
(define block-size (if small? 64 4096))

(define chrome-setup 
  (list
   (creat 0)  ; fd 0
   (write 0 (for/list ([i (first writes)]) #t))
   (fsync 0)))

(define chrome-test
  (list
   (write 0 (for/list ([i (second writes)]) #t))
   (write 0 (for/list ([i (third writes)]) #t))))

; SeqFS
(define (chrome-allow oldfs newfs)
  ; file must be a prefix of #ts
  (define new-0 (ondisk newfs 0))
  (list (apply && new-0)))

(define (chrome-fs-seqfs)
  (seq-fs 2))

; Ext4
(define (chrome-fs-ext4)
  (ext4-fs #:capacity 2 #:blocksize block-size))
(define (chrome-fs-ext4-nodelalloc)
  (ext4-fs #:capacity 2 #:blocksize block-size #:nodelalloc? #t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (test-seqfs)
  (printf "test-seqfs\n")
  (define test
    (litmus chrome-fs-seqfs chrome-setup chrome-test chrome-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 3)
  )

(define (test-ext4)
  (printf "test-ext4 ~a\n" small?)
  (printf "  verify-correctness\n")
  (define test
    (litmus chrome-fs-ext4 chrome-setup chrome-test chrome-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (sat? cex))
  (printf "  all-states\n")
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 7)
  )

(define (test-ext4-nodelalloc)
  (printf "test-ext4-nodelalloc ~a\n" small?)
  (printf "  verify-correctness\n")
  (define test
    (litmus chrome-fs-ext4-nodelalloc chrome-setup chrome-test chrome-allow))
  (define-values (cex state) (verify-correctness test))
  (check-true (unsat? cex))
  (check-false state)
  (printf "  all-states\n")
  (define all-states (all-outcomes test))
  (check equal? (length all-states) 4)
  )

(define (test-ext4-synth)
  (printf "test-ext4-synth ~a\n" small?)
  (define test
    (litmus chrome-fs-ext4 chrome-setup chrome-test chrome-allow))
  (define prog (synth test))
  (check-true (false? prog)))  ; no fences will fix this program

(define (test-ext4-synth-nodelalloc)
  (printf "test-ext4-synth-nodelalloc ~a\n" small?)
  (printf "  synth\n")
  (define test
    (litmus chrome-fs-ext4-nodelalloc chrome-setup chrome-test chrome-allow))
  (define prog (synth test))
  (check-false (false? prog))
  (check-false (term? prog))
  (define cost (sync-cost prog))
  (check equal? cost 0)  ; program is already correct with nodelalloc; no fences needed
  (printf "  verify-correctness\n")
  (define test*
    (litmus chrome-fs-ext4-nodelalloc chrome-setup prog chrome-allow))
  (define-values (cex state) (verify-correctness test*))
  (check-true (unsat? cex)))

(define chrome-tests
  (test-suite
   "chrome litmus test"
   #:before (thunk (printf "-----chrome-----\n"))
   (test-seqfs)
   (test-ext4)
   (test-ext4-nodelalloc)
   ))

(define chrome-synth-tests
  (test-suite
   "chrome synth test"
   #:before (thunk (printf "-----chrome synth-----\n"))
   (test-ext4-synth)
   (test-ext4-synth-nodelalloc)
   ))

(time (run-tests chrome-tests))  ; small? = #f: passes in 72s
(time (run-tests chrome-synth-tests))  ; small? = #f: passes in 195s
