#lang s-exp rosette

(require "fs.rkt" "nondet.rkt")

(provide (all-defined-out))

; Litmus tests are written as lists of syscalls.
(struct syscall () #:transparent)
(struct creat syscall (fd) #:transparent)
(struct write syscall (fd content) #:transparent)
(struct rename syscall (old new) #:transparent)
(struct efsync syscall (fd enabled) #:transparent)
(define (fsync fd) (efsync fd #t))

; A file system compiles a program of syscalls into a program of inode-ops.
; These structs are mutable to prevent Rosette from merging them.
; The problem is that if the instructions are merged, the operands can be
; symbolic, and the operands of some ops are used in forms like (take ...),
; which perform poorly when all operands are symbolic.
; Making the structs mutable forces them to be concrete when they reach the
; file system's (execute ...) form.
(struct inode-op (ino) #:transparent #:mutable)
(struct i-dir-add inode-op (fd) #:transparent #:mutable)
(struct i-dir-rename inode-op (dst) #:transparent #:mutable)
(struct i-file-write inode-op (content offset) #:transparent #:mutable)
(struct i-swap inode-op (enabled) #:transparent #:mutable)
(struct i-file-setsize inode-op (size) #:transparent #:mutable)
(struct i-file-extend inode-op (content offset size) #:transparent #:mutable)


; Test if two ops are directory ops on the same directory.
; Since a file system only models a single directory, we need only
; check that they are both directory ops.
(define (dir-same-ino-deps? op1 op2)
  (and (or (i-dir-add? op1) (i-dir-rename? op1))
       (or (i-dir-add? op2) (i-dir-rename? op2))))

; Test if either of the ops is a barrier.
; TODO: this is too strong -- fsync only blocks reordering with its own fd.
; (also a problem in the Python version)
(define (barrier-deps? op1 op2)
  (or (and (i-swap? op1) (i-swap-enabled op1))
      (and (i-swap? op2) (i-swap-enabled op2))))

; Tests if two ops are file ops that operate on the same file.
(define (file-same-ino-deps? op1 op2)
  (or (equal? (inode-op-ino op1) (inode-op-ino op2))
      (and (i-dir-rename? op1) (equal? (i-dir-rename-dst op1) (inode-op-ino op2)))
      (and (i-dir-rename? op2) (equal? (i-dir-rename-dst op2) (inode-op-ino op1)))
      (and (i-dir-rename? op1) (i-dir-rename? op2) (equal? (i-dir-rename-dst op1) (i-dir-rename-dst op2)))
      (and (i-dir-add? op1) (equal? (i-dir-add-fd op1) (inode-op-ino op2)))
      (and (i-dir-add? op2) (equal? (i-dir-add-fd op2) (inode-op-ino op1)))))

; Tests if two ops are metadata updates that operate on the same file.
(define (metadata-same-ino-deps? op1 op2)
  (and (or (i-file-setsize? op1) (i-file-extend? op1))
       (or (i-file-setsize? op2) (i-file-extend? op2))
       (equal? (inode-op-ino op1) (inode-op-ino op2))))

; Tests if two ops are writes that operate on the same block.
(define (same-file-block-deps? op1 op2 block-size)
  (define should-check?
    (and (or (i-file-write? op1) (i-file-extend? op1))
         (or (i-file-write? op2) (i-file-extend? op2))
         (equal? (inode-op-ino op1) (inode-op-ino op2))))
  (if (not should-check?) #f
      (begin
        (define op1-off (if (i-file-write? op1) (i-file-write-offset op1) (i-file-extend-offset op1)))
        (define op2-off (if (i-file-write? op2) (i-file-write-offset op2) (i-file-extend-offset op2)))
        (define op1-size (length (if (i-file-write? op1) (i-file-write-content op1) (i-file-extend-content op1))))
        (define op2-size (length (if (i-file-write? op2) (i-file-write-content op2) (i-file-extend-content op2))))
        (define op1-block (if (= (remainder op1-off block-size) 0)
                              op1-off
                              (- op1-off (remainder op1-off block-size))))
        (define op2-block (if (= (remainder op2-off block-size) 0)
                              op2-off
                              (- op2-off (remainder op2-off block-size))))
        (= op1-block op2-block))))

; Tests if op1 is an earlier write to a file, and op2 allocates a new
; block of the same file.
(define (file-write-extend-deps? op1 op2 nodelalloc?)
  (and (i-file-write? op1)
       (or (i-file-extend? op2) (and nodelalloc? (i-file-setsize? op2)))
       (equal? (inode-op-ino op1) (inode-op-ino op2))))

; Execute a program of inode-ops against a given file system.
; The operations are performed in the order given by `order`;
; e.g., if order = '(1 0 2) then `prog` is reordered so that the
;   second op runs before the first.
; If crash? is true, the program can also non-deterministically crash
; before executing each operation.
(define (interpret 
         #:program prog
         #:filesystem fs
         #:order [order (range (length prog))]
         #:crash? [crash? #t])
  (let loop ([i 0] [fs fs])
    (if (and crash? ((nondet) boolean?))
        fs
        (begin
          (define op (list-ref prog (list-ref order i)))
          (define fs* (execute fs op))
          (if (< i (sub1 (length order)))
              (loop (add1 i) fs*)
              fs*)))))

; Determine if a reordering is valid according to the given filesystem.
(define (valid-ordering fs prog order)
  (and
   (apply &&
    (for/list ([i (length order)])
     (= (apply + (for/list ([j order]) (if (= i j) 1 0))) 1)))
   (apply &&
    (for*/list ([i (length order)][j (in-range (add1 i) (length order))])
     (define idx-i (list-ref order i))
     (define op-i (list-ref prog idx-i))
     (define idx-j (list-ref order j))
     (define op-j (list-ref prog idx-j))
     (=> (> idx-i idx-j) (and (reorder? fs op-i op-j) (reorder? fs op-j op-i)))))))

; Produce a list of all valid reorderings of a program according to the given filesystem.
(define (all-valid-orderings fs prog)
  (define-symbolic* order integer? [(length prog)])
  (let loop ([orders '()] [asserts '(#t)])
    (define S (solve (assert (and (valid-ordering fs prog order)
                                  (apply && asserts)))))
    (cond [(sat? S) (define o (evaluate order S))
                    (define a (not (equal? order o)))
                    (loop (append orders (list o)) (append asserts (list a)))]
          [else     orders])))

; Convert an ordering `lst` into a model for the order variables in `order`.
(define (ordering->model order lst)
  (sat (for/hash ([o order][l lst])
         (values o l))))

; Insert symbolic fsync operations between each syscall in a given program.
; If (length prog) = n, then the returned program has length 2n+1,
; where a sync is inserted between each op in `prog` and also before the first
; and after the last ops.
(define (insert-synth-syncs prog)
  (define-symbolic* sync0? boolean?)
  (define-symbolic* fd0 integer?)
  (for/fold ([ops (list (efsync fd0 sync0?))])
            ([op prog])
    (define-symbolic* sync? boolean?)
    (define-symbolic* fd integer?)
    (values (append ops (list op (efsync fd sync?))))))

; Remove unused fsync operations (i.e., efsync syscalls with (efsync-enabled e) = #f)
; from a given program
(define (remove-disabled-syncs prog)
  (filter (lambda (s) (not (and (efsync? s) (not (efsync-enabled s))))) prog))
