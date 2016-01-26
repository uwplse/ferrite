#lang s-exp rosette

(require "fs.rkt" "lang.rkt" "litmus.rkt" "nondet.rkt"
         (only-in rosette/base/bool @boolean?)
         (only-in rosette/base/num @number?))

(provide (all-defined-out))

; Ensure that every symbolic value in prog is bound
(define (bind-all-syncs prog model)
  (sat (for/hash ([s (symbolics prog)])
         (match (model s)
           [(constant _ (== @number?)) (values s 0)]
           [(constant _ (== @boolean?)) (values s #f)]
           [val (values s val)]))))

; Measure the synchronization cost of a program; i.e., the number
; of fsync operations that execute.
(define (sync-cost prog)
  (apply + (for/list ([op prog]) 
             (match op 
               [(efsync fd e) (if e 1 0)]
               [_ 0]))))

; Synthesize a program that makes the given litmus test valid.
; @returns (or/c (listof syscall? #f), where the result is a program
;          that makes the litmus test valid if one exists, or #f otherwise.
(define (synth test)
  (clear-asserts)
  (match-define (litmus make-fs setup prog allow) test)
  (define fs (make-fs))
  (when (> (length setup) 0)
    (set! setup (crack fs setup))
    (set! fs (interpret #:program setup
                        #:filesystem fs
                        #:crash? #f)))
  
  (define prog-with-syncs (insert-synth-syncs prog))
  (define prog+ (crack fs prog-with-syncs))
  
  (define-symbolic* order number? [(length prog+)])
  
  (define crashes (choices))
  (define newfs
    (parameterize ([nondet crashes])
      (interpret #:program prog+
                 #:filesystem fs
                 #:order order)))
  
  (define allowed (allow fs newfs))
  
  (define C (sync-cost prog-with-syncs))
  
  (let loop ([sol #f] [cost +inf.0])
    (define cost-constraint (if (infinite? cost) #t (< C cost)))
    (define S
      (with-handlers ([exn:fail? (const (unsat))])
        (synthesize #:forall (append (all-choices crashes) order)
                    #:guarantee (assert (=> (valid-ordering newfs prog+ order)
                                            (and (apply || allowed)
                                                 cost-constraint))))))
    (cond [(sat? S)  (set! S (bind-all-syncs prog-with-syncs S))
                     (define S+ (evaluate prog-with-syncs S))
                     (define C+ (evaluate C S))
                     (loop S+ C+)]
          [else      sol])))
