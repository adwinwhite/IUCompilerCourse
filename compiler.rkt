#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (uniquify-name env)
  (lambda (x)
    (string->symbol (string-append 
      (symbol->string x) 
      (number->string 
        (add1 (if (dict-has-key? env x)
          (string->number
                (substring (symbol->string (dict-ref env x))
                           (string-length (symbol->string x))
                           ))
          0
          )))))))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let* ([unique-name ((uniquify-name env) x)]
              [new-env (dict-set env x unique-name)])
         (Let unique-name ((uniquify-exp new-env) e) ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))


(define remove-complex-opera-exp
  (lambda (e)
    (match e
      [(Var x)
       (Var x)]
      [(Int n) (Int n)]
      [(Let x e body)
       (Let x (remove-complex-opera-exp e) (remove-complex-opera-exp body))]
      [(Prim '- (list e))
        (if (atm? e) 
          (Prim '- (list e))
          (Let 'tmp (remove-complex-opera-exp e) (Prim '- (list (Var 'tmp)))))]
      [(Prim op (list e1 e2))
        (match (cons (atm? e1) (atm? e2))
          [(cons #t #t)
           (Prim op (list e1 e2))]
          [(cons #t #f)
           (Let 'tmp (remove-complex-opera-exp e2) (Prim op (list e1 (Var 'tmp))))]
          [(cons #f #t)
           (Let 'tmp (remove-complex-opera-exp e1) (Prim op (list (Var 'tmp) e2)))]
          [(cons #f #f)
            (Let 'tmp1 (remove-complex-opera-exp e1) (
              Let 'tmp2 (remove-complex-opera-exp e2) (
                Prim op (list (Var 'tmp1) (Var 'tmp2)))))])])))



;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) (remove-complex-opera-exp e)))]))

(define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate_assign unhandled case" e)]))

(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate_tail unhandled case" e)]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e) (CProgram info (dict-set '() 'start  (explicate_tail e)))]))

(define (atm->args a)
  (match a
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    [else (error "not atm" a)]))

(define (assign-arg->instrs arg exp)
  (match exp
    [(? atm?) (list (Instr 'movq (list (atm->args exp) arg)))]
    [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) arg)))]
    [(Prim '- (list e)) (list (Instr 'movq (list (atm->args e) arg)) (Instr 'negq (list arg)))]
    [(Prim '+ (list e1 e2)) (list (Instr 'movq (list (atm->args e1) arg)) (Instr 'addq (list (atm->args e2) arg)))]
    [(Prim '- (list e1 e2)) (list (Instr 'movq (list (atm->args e1) arg)) (Instr 'subq (list (atm->args e2) arg)))]
    [else (error "invalid expression in assignment statement" exp)]))



(define (stmt->instrs s)
  (match s
    [(Assign x exp) (let ([arg (atm->args x)]) (assign-arg->instrs arg exp))]
    [else (error "stmt->instrs unhandled statements" s)]))
  

(define (ret->instrs e)
  (append (assign-arg->instrs (Reg 'rax) e) (list (Jmp 'conclusion))))

(define (tail->instrs t)
  (match t
    [(Seq fst snd) (append (stmt->instrs fst) (tail->instrs snd))]
    [(Return e) (append (ret->instrs e) '())]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info (list (cons label tail))) (X86Program info (dict-set '() 'start  (Block info (tail->instrs tail))))]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
