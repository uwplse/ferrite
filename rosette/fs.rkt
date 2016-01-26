#lang s-exp rosette

(require racket/generic)

(provide (all-defined-out))

; A file system is an immutable set of files in a single directory.
; File names are modeled as numbers.
;
; Programs operate on a file system by passing an inode-op? to execute,
; which returns a new file system reflecting the updated state.
;
; File systems also control the compilation of programs to inode-ops.
; Passing a list of syscalls to crack returns a list of inode-ops
; corresponding to that program.
;
; Finally, a file system dictates whether two inode-op?s can be reordered
; with each other, according to the reorder? procedure.
(define-generics filesystem
  ; Compiles a program of syscalls into a program of inode-ops.
  ; crack : (listof syscall?) → (listof inode-op?)
  (crack filesystem prog)
  
  ; Executes the inode-op? on this file system and returns the resulting
  ; file system.
  ; execute : inode-op? → filesystem?
  (execute filesystem op)
  
  ; Returns the on-disk contents of a file of the given name, or #f if
  ; the file does not exist.
  ; ondisk : number? → (or/c (listof boolean?) #f)
  (ondisk filesystem name)
  
  ; Returns #t if the inode-op?s op1 and op2 are allowed to be reordered
  ; with each other, or #f otherwise.
  ; reorder? : inode-op? → inode-op? → boolean?
  (reorder? filesystem op1 op2)

  ; Returns #t if this file system is observationally equivalent to the given
  ; file system, or #f otherwise.
  ; Two file systems are observationaly equivalent if they contain the same files
  ; with the same on-disk contents.
  ; obs-equal? : filesystem? → boolean?
  (obs-equal? filesystem other)
  
  )
