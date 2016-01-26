#lang s-exp rosette

(provide litmus)

; A litmus test consists of:
; * fs : void -> filesystem?  constructs a new filesystem to execute the test
;   against.
; * setup : (listof? syscall?)  is the initial program to run against the filesystem.
;   This program cannot crash nor be reordered.
; * test : (listof? syscall?)  is the main body of the litmus test.
; * allowed : (listof term?)  is a list of allowed states that will be checked
;   against the final state of the file system. Every possible final state of the
;   file system must make at least one term in allowed true; in other words,
;   a litmus tests checks that  
;      ∀ trace. Valid(trace) ⇒ a_1 ∨ ⋯ ∨ a_n
;   where allowed = '(a_1 a_2 ... a_n).
(struct litmus (fs setup test allowed) #:transparent)

