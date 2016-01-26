#lang s-exp rosette

(require "fs.rkt" "lang.rkt" rosette/lib/reflect/match)

(provide adv-fs)

(define (adv-fs [cap 3])
  (AdvFS 
   (for/vector #:length cap ([i cap]) (cons i #f))
   (make-vector cap 0)
   (make-vector cap (file '() '()))))

(struct file (ondisk incache) #:transparent)
                     
; Implements HP's AdvFS, which persists file contents to disk only when explicitly forced.
(struct AdvFS (dir fds files)
  #:transparent
  #:methods gen:filesystem
  [
   ; Compiles a program of syscalls into a program of inode-ops.
   ; The important part is that we have to keep track of the current size of the
   ; file pointed to by each `fd`, so that we generate inode-ops with the appropriate
   ; offsets.
   (define (crack self prog)
     (define nextfd 0)
     (match-define (AdvFS dir fds files) self)
     (define lengths (for/hash ([fd (vector-length fds)] [ino fds])
                       (values fd (length (file-incache (vector-ref files ino))))))
     (for/list ([op prog])
       (match op
         [(creat name)         (begin0
                                 (i-dir-add name nextfd)
                                 (let* ([ino (car (vector-ref dir name))]
                                        [cnt (file-ondisk (vector-ref files ino))])
                                   (set! lengths (hash-set lengths nextfd (length cnt))))
                                 (set! nextfd (add1 nextfd)))]
         [(write fd cnt)     (begin0
                               (i-file-write fd cnt (hash-ref lengths fd))
                               (set! lengths (hash-set lengths fd (+ (hash-ref lengths fd) (length cnt)))))]
         [(rename name1 name2)   (i-dir-rename name1 name2)]
         [(efsync fd e)         (i-swap fd e)])))
           
   ; Executes the inode-op? on this file system and returns the resulting
   ; file system.
   (define (execute self call)
     (match-define (AdvFS dir fds files) self)
     (define new-dir (make-vector (vector-length dir)))
     (vector-copy! new-dir 0 dir)
     (define new-fds (make-vector (vector-length fds)))
     (vector-copy! new-fds 0 fds)
     (define new-files (make-vector (vector-length files)))
     (vector-copy! new-files 0 files)
     (match call
       [(i-dir-add name fd)     (match-define (cons ino exists?) (vector-ref dir name))
                                (vector-set! new-files ino (file '() '()))
                                (vector-set! new-dir name (cons ino #t))
                                (vector-set! new-fds fd ino)]
       [(i-file-write fd cnt off)   (define ino (vector-ref fds fd))
                                    (match-define (file ondisk incache) (vector-ref files ino))
                                    (define off-end (+ off (length cnt)))
                                    (when (> off (length incache))
                                      (set! incache (append incache (for/list ([i (- off (length incache))]) #f))))
                                    (define head (take incache off))
                                    (define tail (if (< off-end (length incache)) (drop incache off-end) '()))
                                    (define newc (append head cnt tail))
                                    (define newf (file ondisk newc))  ; write to incore only
                                    (vector-set! new-files ino newf)]
       [(i-dir-rename name1 name2)  (unless (= name1 name2)
                                      (define new-ino (car (vector-ref dir name1)))
                                      (define old-ino (car (vector-ref dir name2)))
                                      (vector-set! new-files old-ino (file '() '()))
                                      (vector-set! new-dir name1 (cons old-ino #f))
                                      (vector-set! new-dir name2 (cons new-ino #t)))]
       [(i-swap fd enabled)  (when (and enabled (>= fd 0) (< fd (vector-length fds)))  ; sync to disk
                               (define ino (vector-ref fds fd))
                               (match-define (file ondisk incache) (vector-ref files ino))
                               (vector-set! new-files ino (file incache incache)))])
     (AdvFS new-dir new-fds new-files))
   
   ; Returns the on-disk contents of a file of the given name, or #f if
   ; the file does not exist.
   (define (ondisk self name)
     (match-define (AdvFS dir fds files) self)
     (define ino (car (vector-ref dir name)))
     (define exists? (cdr (vector-ref dir name)))
     (if exists? (file-ondisk (vector-ref files ino)) #f))
   
   ; Returns #t if the inode-op?s op1 and op2 are allowed to be reordered
   ; with each other, or #f otherwise.
   (define (reorder? self call1 call2)
     (and
      (not (dir-same-ino-deps? call1 call2))
      (not (barrier-deps? call1 call2))
      (not (file-same-ino-deps? call1 call2))))

   ; Returns #t if this file system is observationally equivalent to the given
   ; file system, or #f otherwise.
   ; Observational equivalence means we need only check the ondisk state.
   (define (obs-equal? self other)
     (match-define (AdvFS s-dir s-fds s-files) self)
     (match-define (AdvFS o-dir o-fds o-files) other)
     (apply && (for/list ([i (vector-length s-dir)])
                 (define s-ino (car (vector-ref s-dir i)))
                 (define s-exists? (cdr (vector-ref s-dir i)))
                 (define o-ino (car (vector-ref o-dir i)))
                 (define o-exists? (cdr (vector-ref o-dir i)))
                 (define s-file (vector-ref s-files s-ino))
                 (define o-file (vector-ref o-files o-ino))
                 (and (equal? s-exists? o-exists?)
                      (=> s-exists? (equal? (file-ondisk s-file) (file-ondisk o-file)))))))
   ])