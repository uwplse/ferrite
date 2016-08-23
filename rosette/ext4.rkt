#lang s-exp rosette

(require "fs.rkt" "lang.rkt" rosette/lib/match)

(provide ext4-fs)

; Creates an instance of the ext4 model with the given parameters.
(define (ext4-fs #:capacity [cap 3] #:blocksize [bs 4096] #:nodelalloc? [nodelalloc? #f])
  (Ext4FS 
   bs
   nodelalloc?
   (for/vector #:length cap ([i cap]) (cons i #f))
   (make-vector cap 0)
   (make-vector cap (file (fsize 0) '()))))

(define (roundup x BLOCK_SIZE)
  (if (= (remainder x BLOCK_SIZE) 0)
      x
      (- (+ x BLOCK_SIZE) (remainder x BLOCK_SIZE))))

(struct file (size ondisk) #:transparent)
(struct fsize (size) #:transparent #:mutable)  ; hack to force size to be a union instead of an expr

; Implements a model of ext4, with optional delayed allocation.
(struct Ext4FS (BLOCK_SIZE nodelalloc? dir fds files)
  #:transparent
  #:methods gen:filesystem
  [
   ; Compiles a program of syscalls into a program of inode-ops.
   ; The logic is complex because we must compile a `write` into multiple writes/extends
   ; at the block granularity.
   (define (crack self prog)
     (define nextfd 0)
     (match-define (Ext4FS BLOCK_SIZE nodelalloc? dir fds files) self)
     ; Tracks the *actual* length of the file
     (define lengths (for/hash ([fd (vector-length fds)] [ino fds])
                       (values fd (fsize-size (file-size (vector-ref files ino))))))
     ; Tracks the block length of the file -- i.e., the number of bytes allocated
     (define block-lengths (for/hash ([fd (vector-length fds)] [ino fds])
                             (values fd (length (file-ondisk (vector-ref files ino))))))
     (flatten
      (for/list ([op prog])
       (match op
         [(creat name)       (begin0
                               (i-dir-add name nextfd)
                               (let* ([ino (car (vector-ref dir name))]
                                      [cnt (file-ondisk (vector-ref files ino))])
                                 (set! lengths (hash-set lengths nextfd (length cnt))))
                               (set! nextfd (add1 nextfd)))]
         [(write fd cnt)     (define offset (hash-ref lengths fd))
                             (define offset-end (+ offset (length cnt)))
                             (define ops '())
                             ; first, fill out the gap from offset to the next block boundary
                             (when (not (= offset (roundup offset BLOCK_SIZE)))
                               (define chunk (take cnt (min (- (roundup offset BLOCK_SIZE) offset) (length cnt))))
                               (set! ops (append ops (list (i-file-write fd chunk offset)
                                                           (i-file-setsize fd (+ offset (length chunk))))))
                               (set! lengths (hash-set lengths fd (+ (hash-ref lengths fd) (length chunk)))))
                             ; now write the rest of the file in block-sized chunks
                             (for ([pos (in-range (roundup offset BLOCK_SIZE) offset-end BLOCK_SIZE)])
                               (define pos-end (+ pos BLOCK_SIZE))
                               (define chunk (drop (take cnt (min (- pos-end offset) (length cnt))) (- pos offset)))
                               (set! lengths (hash-set lengths fd (+ (hash-ref lengths fd) (length chunk))))
                               ; if pos-end <= len(fd), we can write, otherwise we must extend (alloc new blocks)
                               (if (<= pos-end (hash-ref block-lengths fd))
                                   (begin
                                     (set! ops (append ops (list (i-file-write fd chunk pos)
                                                                 (i-file-setsize fd pos-end)))))
                                   (begin
                                     (if (<= (length chunk) BLOCK_SIZE)
                                         (begin
                                           (set! chunk (append chunk (for/list ([i (- BLOCK_SIZE (length chunk))]) #f)))
                                           (set! ops (append ops (list (i-file-extend fd chunk pos offset-end)))))
                                         (set! ops (append ops (list (i-file-extend fd chunk pos pos-end)))))
                                     (set! block-lengths (hash-set block-lengths fd pos-end)))))
                             ops]
         [(rename name1 name2)   (i-dir-rename name1 name2)]
         [(efsync fd e)         (i-swap fd e)]))))
   
   ; Executes the inode-op? on this file system and returns the resulting
   ; file system.
   (define (execute self call)
     (match-define (Ext4FS BLOCK_SIZE nodelalloc? dir fds files) self)
     (define new-dir (make-vector (vector-length dir)))
     (vector-copy! new-dir 0 dir)
     (define new-fds (make-vector (vector-length fds)))
     (vector-copy! new-fds 0 fds)
     (define new-files (make-vector (vector-length files)))
     (vector-copy! new-files 0 files)
     
     ; Perform a write of the given contents at the given offset
     (define (do-write fd cnt off)
       (define ino (vector-ref fds fd))
       (match-define (file size ondisk) (vector-ref files ino))
       (define off-end (+ off (length cnt)))
       (when (> off (length ondisk))
         (set! ondisk (append ondisk (for/list ([i (- off (length ondisk))]) #f))))
       (define head (take ondisk off))
       (define tail (if (< off-end (length ondisk)) (drop ondisk off-end) '()))
       (define newc (append head cnt tail))
       (define newf (file size newc))
       (vector-set! new-files ino newf))
     ; Update the size metadata of a file
     (define (update-size fd size)
       (define ino (vector-ref fds fd))
       (match-define (file s ondisk) (vector-ref new-files ino))
       (define newf (file (fsize size) ondisk))
       (vector-set! new-files ino newf))
     
     (match call
       [(i-dir-add name fd)     (match-define (cons ino exists?) (vector-ref dir name))
                                ;(vector-set! new-files ino (file 0 '()))
                                (vector-set! new-dir name (cons ino #t))
                                (vector-set! new-fds fd ino)]
       [(i-file-write fd cnt off) (do-write fd cnt off)]
       [(i-file-extend fd cnt off size) (do-write fd cnt off)
                                        (update-size fd size)]
       [(i-file-setsize fd size)        (update-size fd size)]
       [(i-dir-rename name1 name2)  (unless (= name1 name2)
                                      (define new-ino (car (vector-ref dir name1)))
                                      (define old-ino (car (vector-ref dir name2)))
                                      (vector-set! new-files old-ino (file (fsize 0) '()))
                                      (vector-set! new-dir name1 (cons old-ino #f))
                                      (vector-set! new-dir name2 (cons new-ino #t)))]
       [(i-swap fd enabled)  (void)])
     (Ext4FS BLOCK_SIZE nodelalloc? new-dir new-fds new-files))
   
   ; Returns the on-disk contents of a file of the given name, or #f if
   ; the file does not exist.
   (define (ondisk self name)
     (match-define (Ext4FS BLOCK_SIZE nodelalloc? dir fds files) self)
     (define ino (car (vector-ref dir name)))
     (define exists? (cdr (vector-ref dir name)))
     (if exists? 
         (begin
           (define file (vector-ref files ino))
           (define content (file-ondisk (vector-ref files ino)))
           (define size (file-size (vector-ref files ino)))
           ; Here, `size` is an instance of the fsize struct.
           ; We perform symbolic reflection on that struct to get all possible
           ; concrete values of the file's size, and perform (take ...) for each one,
           ; generating a symbolic union of the file's possible contents.
           ; If we didn't encapsulate size in a struct, it would be an expression
           ; of type number?, and Rosette would be forced to compile the (take ...)
           ; to a much larger symbolic union -- one guard for every possible 
           ; number? -- because it could not prove that they are infeasible values of size.
           (for/all ([size size])
             (take content (fsize-size size))))
         #f))
   
   ; Returns #t if the inode-op?s op1 and op2 are allowed to be reordered
   ; with each other, or #f otherwise.
   (define (reorder? self call1 call2)
     (match-define (Ext4FS BLOCK_SIZE nodelalloc? dir fds files) self)
     (and
      (not (dir-same-ino-deps? call1 call2))
      (not (barrier-deps? call1 call2))
      (not (metadata-same-ino-deps? call1 call2))
      (not (same-file-block-deps? call1 call2 BLOCK_SIZE))
      (not (file-write-extend-deps? call1 call2 nodelalloc?))))

   ; Returns #t if this file system is observationally equivalent to the given
   ; file system, or #f otherwise.
   (define (obs-equal? self other)
     (match-define (Ext4FS s-BLOCK_SIZE s-nodelalloc? s-dir s-fds s-files) self)
     (match-define (Ext4FS o-BLOCK_SIZE o-nodelalloc? o-dir o-fds o-files) other)
     (apply && (for/list ([i (vector-length s-dir)])
                 (define s-ino (car (vector-ref s-dir i)))
                 (define s-exists? (cdr (vector-ref s-dir i)))
                 (define o-ino (car (vector-ref o-dir i)))
                 (define o-exists? (cdr (vector-ref o-dir i)))
                 (define s-file (vector-ref s-files s-ino))
                 (define o-file (vector-ref o-files o-ino))
                 (and (equal? s-exists? o-exists?)
                      (=> s-exists? (and (equal? (fsize-size (file-size s-file)) (fsize-size (file-size o-file)))
                                         ; The same problem as in (ondisk ...).
                                         (for/all ([size (file-size s-file)])
                                           (equal? (take (file-ondisk s-file) (fsize-size size))
                                                   (take (file-ondisk o-file) (fsize-size size))))))))))
   ])

