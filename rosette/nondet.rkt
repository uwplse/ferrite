#lang racket 

; This module is intentionally implemented in Racket to prevent Rosette from tracking 
; conditional state updates within it. We want to capture every choice invocation 
; (even infeasible ones), rather than only feasible ones.  


(require (only-in rosette define-symbolic*))

(provide nondet
         (rename-out [make-choices choices]
                     [choices-returned all-choices]))

(define (make-choices) 
  (choices '()))

; Implements a struct that acts as a procedure for generating fresh 
; symbolic constants and remembering them, so that they can be recalled 
; later by calling all-choices from an external module.
(struct choices (returned) 
  #:transparent 
  #:mutable
  #:property prop:procedure
  (lambda (self type)
    (define-symbolic* choice type)
    (set-choices-returned! self (cons choice (choices-returned self)))
    choice))
  
  
(define nondet (make-parameter (make-choices)))