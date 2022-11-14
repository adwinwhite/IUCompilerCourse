#lang racket
(require graph)
(require racket/set racket/stream)
(require racket/fixnum)
(require "multigraph.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
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
(define (pe-neg ic)
  (match ic
    [(Int n) (Int (fx- 0 n))]
    [(Prim '- (list ire)) ire]
    [(Prim '+ (list (Int n) ire)) (Prim '- (list (Int (fx- 0 n)) ire))]
    [(Prim '- (list ire (Int n))) (Prim '- (list (Int n) ire))]
    [(Prim '- (list (Int n) ire)) (Prim '- (list ire (Int n)))]
    [else (Prim '- (list ic))]))

(define (pe-add ic1 ic2)
  (match* (ic1 ic2)
    [((Int n1) ic2) (match ic2
                          [(Int n2) (Int (fx+ n1 n2))]
                          [(Prim '- (list ire)) (Prim '- (list (Int n1) ire))]
                          [(Prim '+ (list (Int n2) ire)) (Prim '+ (list (Int (fx+ n1 n2)) ire))]
                          [(Prim '- (list (Int n2) ire)) (Prim '- (list (Int (fx+ n1 n2)) ire))]
                          [(Prim '- (list ire (Int n2))) (Prim '+ (list (Int (fx- n1 n2)) ire))]
                          [else (Prim '+ (list (Int n1) ic2))])]
    [((Prim '- (list ire1)) ic2) (match ic2
                          [(Int n1) (Prim '- (list (Int (fx- 0 n1)) ire1))]
                          [(Prim '- (list ire2)) (Prim '- (list (Prim '+ (list ire1 ire2))))]
                          [(Prim '+ (list (Int n1) ire2)) (Prim '+ (list (Int n1) (Prim '- (list ire2 ire1))))]
                          [(Prim '- (list (Int n1) ire2)) (Prim '- (list (Int n1) (Prim '+ (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n1))) (Prim '+ (list (Int (fx- 0 n1)) (Prim '- (list ire2 ire1))))]
                          [else (Prim '- (list ic2 ire1))])]
    [((Prim '+ (list (Int n1) ire1)) ic2) (match ic2
                          [(Int n2) (Prim '+ (list (Int (fx+ n1 n2)) ire1))]
                          [(Prim '- (list ire2)) (Prim '+ (list (Int n1) (Prim '- (list ire1 ire2))))]
                          [(Prim '+ (list (Int n2) ire2)) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '+ (list ire1 ire2))))]
                          [(Prim '- (list (Int n2) ire2)) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '- (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n2))) (Prim '+ (list (Int (fx- n1 n2)) (Prim '+ (list ire1 ire2))))]
                          [else (Prim '+ (list (Int n1) (Prim '+ (list ire1 ic2))))])]
    [((Prim '- (list (Int n1) ire1)) ic2) (match ic2
                          [(Int n2) (Prim '- (list (Int (fx+ n1 n2)) ire1))]
                          [(Prim '- (list ire2)) (Prim '- (list (Int n1) (Prim '+ (list ire1 ire2))))]
                          [(Prim '+ (list (Int n2) ire2)) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '- (list ire2 ire1))))]
                          [(Prim '- (list (Int n2) ire2)) (Prim '- (list (Int (fx+ n1 n2)) (Prim '+ (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n2))) (Prim '+ (list (Int (fx- n1 n2)) (Prim '- (list ire2 ire1))))]
                          [else (Prim '+ (list (Int n1) (Prim '- (list ic2 ire1))))])]
    [((Prim '- (list ire1 (Int n1))) ic2) (match ic2
                          [(Int n2) (Prim '+ (list (Int (fx- n2 n1)) ire1))]
                          [(Prim '- (list ire2)) (Prim '+ (list (Int (fx- 0 n1)) (Prim '- (list ire1 ire2))))]
                          [(Prim '+ (list (Int n2) ire2)) (Prim '+ (list (Int (fx- n2 n1)) (Prim '+ (list ire1 ire2))))]
                          [(Prim '- (list (Int n2) ire2)) (Prim '+ (list (Int (fx- n2 n1)) (Prim '- (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n2))) (Prim '- (list (Prim '+ (list ire1 ire2)) (Int (fx+ n1 n2))))]
                          [else (Prim '- (list (Prim '+ (list ire1 ic2)) (Int n1)))])]
    [(ire1 ic2) (match ic2
                          [(Int n1) (Prim '+ (list (Int n1) ire1))]
                          [(Prim '- (list ire2)) (Prim '- (list ire1 ire2))]
                          [(Prim '+ (list (Int n1) ire2)) (Prim '+ (list (Int n1) (Prim '+ (list ire1 ire2))))]
                          [(Prim '- (list (Int n1) ire2)) (Prim '+ (list (Int n1) (Prim '- (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n1))) (Prim '- (list (Prim '+ (list ire1 ire2)) (Int n1)))]
                          [else (Prim '+ (list ire1 ic2))])]))

(define (pe-sub ic1 ic2)
  (match* (ic1 ic2)
    [((Int n1) ic2) (match ic2
                          [(Int n2) (Int (fx- n1 n2))]
                          [(Prim '- (list ire)) (Prim '+ (list (Int n1) ire))]
                          [(Prim '+ (list (Int n2) ire)) (Prim '- (list (Int (fx- n1 n2)) ire))]
                          [(Prim '- (list (Int n2) ire)) (Prim '+ (list (Int (fx- n1 n2)) ire))]
                          [(Prim '- (list ire (Int n2))) (Prim '- (list (Int (fx+ n1 n2)) ire))]
                          [else (Prim '- (list (Int n1) ic2))])]
    [((Prim '- (list ire1)) ic2) (match ic2
                          [(Int n1) (Prim '- (list (Int (fx- 0 n1)) ire1))]
                          [(Prim '- (list ire2)) (Prim '- (list ire2 ire1))]
                          [(Prim '+ (list (Int n1) ire2)) (Prim '- (list (Int (fx- 0 n1)) (Prim '+ (list ire2 ire1))))]
                          [(Prim '- (list (Int n1) ire2)) (Prim '- (list (Int (fx- 0 n1)) (Prim '- (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n1))) (Prim '- (list (Int n1) (Prim '+ (list ire2 ire1))))]
                          [else (Prim '- (list (Prim '+ (list (ic2 ire1)))))])]
    [((Prim '+ (list (Int n1) ire1)) ic2) (match ic2
                          [(Int n2) (Prim '+ (list (Int (fx- n1 n2)) ire1))]
                          [(Prim '- (list ire2)) (Prim '+ (list (Int n1) (Prim '+ (list ire1 ire2))))]
                          [(Prim '+ (list (Int n2) ire2)) (Prim '+ (list (Int (fx- n1 n2)) (Prim '- (list ire1 ire2))))]
                          [(Prim '- (list (Int n2) ire2)) (Prim '+ (list (Int (fx- n1 n2)) (Prim '+ (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n2))) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '- (list ire1 ire2))))]
                          [else (Prim '+ (list (Int n1) (Prim '- (list ire1 ic2))))])]
    [((Prim '- (list (Int n1) ire1)) ic2) (match ic2
                          [(Int n2) (Prim '- (list (Int (fx- n1 n2)) ire1))]
                          [(Prim '- (list ire2)) (Prim '+ (list (Int n1) (Prim '- (list ire2 ire1))))]
                          [(Prim '+ (list (Int n2) ire2)) (Prim '- (list (Int (fx- n1 n2)) (Prim '+ (list ire2 ire1))))]
                          [(Prim '- (list (Int n2) ire2)) (Prim '- (list (Int (fx- n1 n2)) (Prim '- (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n2))) (Prim '- (list (Int (fx+ n1 n2)) (Prim '+ (list ire2 ire1))))]
                          [else (Prim '- (list (Int n1) (Prim '+ (list ic2 ire1))))])]
    [((Prim '- (list ire1 (Int n1))) ic2) (match ic2
                          [(Int n2) (Prim '- (list ire1 (Int (fx+ n2 n1))))]
                          [(Prim '- (list ire2)) (Prim '- (list (Prim '+ (list ire1 ire2)) (Int n1)))]
                          [(Prim '+ (list (Int n2) ire2)) (Prim '- (list (Prim '- (list ire1 ire2)) (Int (fx+ n1 n2))))]
                          [(Prim '- (list (Int n2) ire2)) (Prim '- (list (Prim '+ (list ire1 ire2)) (Int (fx+ n1 n2))))]
                          [(Prim '- (list ire2 (Int n2))) (Prim '+ (list (Int (fx- n2 n1)) (Prim '- (list ire1 ire2))))]
                          [else (Prim '+ (list (Int (fx- 0 n1)) (Prim '- (list ire1 ic2))))])]
    [(ire1 ic2) (match ic2
                          [(Int n1) (Prim '- (list ire1 (Int n1)))]
                          [(Prim '- (list ire2)) (Prim '+ (list ire1 ire2))]
                          [(Prim '+ (list (Int n1) ire2)) (Prim '+ (list (Int (fx- 0 n1)) (Prim '- (list ire1 ire2))))]
                          [(Prim '- (list (Int n1) ire2)) (Prim '+ (list (Int (fx- 0 n1)) (Prim '+ (list ire1 ire2))))]
                          [(Prim '- (list ire2 (Int n1))) (Prim '+ (list (Int n1) (Prim '- (list ire1 ire2))))]
                          [else (Prim '- (list ire1 ic2))])]))

;; Only returns (+ n x) or (- x n) or (- n x). neg -> sub.
(define (pe-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))]
    [(Let x exp body) (Let x (pe-exp exp) (pe-exp body))]
    [else e]))
    

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

(define (shrink-logical e)
  (match e
    [(Prim 'and (list e1 e2)) (If (shrink-logical e1) (shrink-logical e2) (Bool #f))]
    [(Prim 'or (list e1 e2)) (If (shrink-logical e1) (Bool #t) (shrink-logical e2))]
    [(Prim op es) (Prim op (map shrink-logical es))]
    [(Let x exp body) (Let x (shrink-logical exp) (shrink-logical body))]
    [(If cnd thn els) (If (shrink-logical cnd) (shrink-logical thn) (shrink-logical els))]
    [else e]))


(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-logical e))]))

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
      [(Bool b) (Bool b)]
      [(Let x e body)
       (let* ([unique-name ((uniquify-name env) x)]
              [new-env (dict-set env x unique-name)])
         (Let unique-name ((uniquify-exp new-env) e) ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))


(define remove-complex-opera-exp
  (lambda (e)
    (match e
      [(Let x e body)
       (Let x (remove-complex-opera-exp e) (remove-complex-opera-exp body))]
      [(Prim op (list e))
        (if (atm? e) 
          (Prim op (list e))
          (Let 'tmp (remove-complex-opera-exp e) (Prim op (list (Var 'tmp)))))]
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
                Prim op (list (Var 'tmp1) (Var 'tmp2)))))])]
      [(If cnd thn els) (If (remove-complex-opera-exp cnd) (remove-complex-opera-exp thn) (remove-complex-opera-exp els))]
      [else e])))



;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) (remove-complex-opera-exp e)))]))

(define (explicate_assign blocks)
  (lambda (e x cont)
    (match e
      [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
      [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
      [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
      [(Let y rhs body) ((explicate_assign blocks) rhs y ((explicate_assign blocks) body x cont))]
      [(If cnd thn els) ((explicate_pred blocks) cnd ((explicate_assign blocks) thn x cont) ((explicate_assign blocks) els x cont))]
      [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
      [else (error "explicate_assign unhandled case" e)])))

(define (explicate_tail blocks)
  (lambda (e)
    (match e
      [(Var x) (Return (Var x))]
      [(Int n) (Return (Int n))]
      [(Bool b) (Return (Bool b))]
      [(Let x rhs body) ((explicate_assign blocks) rhs x ((explicate_tail blocks) body))]
      [(If cnd thn els) ((explicate_pred blocks) cnd ((explicate_tail blocks) thn) ((explicate_tail blocks) els))]
      [(Prim op atms) (Return (Prim op atms))]
      [else (error "explicate_tail unhandled case" e)])))

(define (create_block blocks) 
  (lambda (tail)
    (match tail
      [(Goto label) (Goto label)]
      [else
        (let ([label (gensym 'block)])
          (dict-set! blocks label tail)
          (Goto label))])))


(define cmp-op '(eq? < <= > >=))

(define cmp-set '(sete setl setle setg setge))

(define cmp-cc '(e l le g ge))

(define cmp-jmp '(je jl jle jg jge))

(define cmp-op-set (map cons cmp-op cmp-set))

(define cmp-op-jmp (map cons cmp-op cmp-jmp))

(define cmp-op-cc (map cons cmp-op cmp-cc))

;; (exp-bool, tail, tail) -> tail
(define (explicate_pred blocks)
  (lambda (cnd thn els)
    (match cnd
      [(Var x) 
        (IfStmt (Prim 'eq? (list (Var x) (Bool #t)))
                ((create_block blocks) thn)
                ((create_block blocks) els))]
      [(Let x rhs body) 
        ((explicate_assign blocks) rhs x ((explicate_pred blocks) body thn els))]
      [(Prim 'not (list e))
        ((explicate_pred blocks) e els thn)]
      [(Prim op es) #:when (member op cmp-op)
        (IfStmt (Prim op es) 
        ((create_block blocks) thn)
        ((create_block blocks) els))]
      [(Bool b) (if b thn els)]
      [(If cnd-inn thn-inn els-inn) 
        (let ([outer-thn ((create_block blocks) thn)]
              [outer-els ((create_block blocks) els)])
          ((explicate_pred blocks) cnd-inn
                          ((explicate_pred blocks) thn-inn outer-thn outer-els)
                          ((explicate_pred blocks) els-inn outer-thn outer-els)))]
      [else (error "explicate_pred unhandled case" cnd)])))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e) (CProgram info (let ([basic-blocks (make-hash)])
                                       (begin
                                         (dict-set! basic-blocks (cp-label 'start) ((explicate_tail basic-blocks) e))
                                         basic-blocks)))]))

(define (atm->args a)
  (match a
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    [(Bool b) (if b (Imm 1) (Imm 0))]
    [else (error "not atm" a)]))

(define (stmt->instrs s)
  (match s
    [(Assign x exp) (match exp
                      [(? atm?) (list (Instr 'movq (list (atm->args exp) x)))]
                      [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
                      [(Prim '- (list e)) (if (equal? e x)
                                            (list (Instr 'negq (list x)))
                                            (list (Instr 'movq (list (atm->args e) x)) (Instr 'negq (list x))))]
                      [(Prim '+ (list e1 e2)) (cond
                                                [(equal? e1 x)
                                                 (list (Instr 'addq (list (atm->args e2) x)))]
                                                [(equal? e2 x)
                                                 (list (Instr 'addq (list (atm->args e1) x)))]
                                                [else
                                                 (list (Instr 'movq (list (atm->args e1) x)) (Instr 'addq (list (atm->args e2) x)))])]
                      [(Prim '- (list e1 e2)) (if (equal? e1 x)
                                                (list (Instr 'subq (list (atm->args e2) x)))
                                                (list (Instr 'movq (list (atm->args e1) x)) (Instr 'subq (list (atm->args e2) x))))]
                      [(Prim 'not (list e)) (if (equal? e x)
                                              (list (Instr 'xorq (list (Imm 1) x)))
                                              (list (Instr 'movq (list (atm->args e) x)) (Instr 'xorq (list (Imm 1) x))))]
                      [(Prim op (list e1 e2)) #:when (member op cmp-op)
                                              (list (Instr 'cmpq (list (atm->args e2) (atm->args e1)))
                                                    (Instr 'set (list (dict-ref cmp-op-cc op) (ByteReg 'al)))
                                                    (Instr 'movzbq (list (ByteReg 'al) x)))]
                      [else (error "unhandled expression in assignment statement" exp)])]
    [else (error "stmt->instrs unhandled statements" s)]))

(define (tail->instrs t)
  (match t
    [(Return e) (append
                  (stmt->instrs (Assign (Reg 'rax) e))
                  (list (Jmp 'conclusion)))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim op (list e1 e2)) (Goto label1) (Goto label2)) 
             (list
               (Instr 'cmpq (list (atm->args e2) (atm->args e1)))
               (JmpIf (dict-ref cmp-op-cc op) label1)
               (Jmp label2))]
    [(Seq fst snd) (append (stmt->instrs fst) (tail->instrs snd))]
    ))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info blocks) 
     (X86Program info (dict-map/copy blocks (lambda (label tail)
                                              (values label (Block '() (tail->instrs tail))))))]))

(define (filter-imm s)
  (list->set (filter (lambda (e)
                       (match e
                         [(Imm _) #f]
                         [else #t]))
                     (set->list s))))

(define (write-locs instr)
  (let ([args (match instr
                [(Instr op (list arg1 arg2)) #:when (member op '(subq addq xorq movq movzbq))
                 (set arg2)]
                [(Instr 'negq (list arg1))
                 (set arg1)]
                [(Instr 'pushq (list arg1))
                 (set)]
                [(Instr 'cmpq (list arg1 arg2))
                 (set)]
                [(Instr 'set (list cc arg1))
                 (set (Reg (byte-reg->full-reg (ByteReg-name arg1))))]
                [(Instr 'popq (list arg1))
                 (set arg1)]
                [(Callq label arity)
                 (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
                [Retq
                 (set)]
                [(or (Jmp label) (JmpIf _ label))
                 (set)]
                )])
    (filter-imm args)))


    

(define ((read-locs env) instr)
  (let ([args (match instr
                [(Instr op (list arg1 arg2)) #:when (member op '(subq addq xorq cmpq)) 
                 (set arg1 arg2)]
                [(Instr 'negq (list arg1))
                 (set arg1)]
                [(Instr 'movq (list arg1 arg2))
                 (set arg1)]
                [(Instr 'movzbq (list arg1 arg2))
                 (set (Reg (byte-reg->full-reg (ByteReg-name arg1))))]
                [(Instr 'pushq (list arg1))
                 (set arg1)]
                [(Instr 'popq (list arg1))
                 (set)]
                [(Instr 'set (list cc arg1))
                 (set)]
                [(Callq label arity)
                 (match arity
                   [0 (set)]
                   [1 (set (Reg 'rdi))]
                   [2 (set (Reg 'rdi) (Reg 'rsi))]
                   [3 (set (Reg 'rdi) (Reg 'rsi) (Reg 'rdx))]
                   [4 (set (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx))]
                   [5 (set (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8))]
                   [6 (set (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9))]
                   [n (list->set (map (lambda (x)
                                        Deref 'rbp (+ 16 (* 8 x)))
                                      (stream->list (in-range (- n 6)))))])]
                [(struct Retq _)
                 (set (Reg 'rax))]
                [(or (Jmp label) (JmpIf _ label))
                 (car (dict-ref env label))]
                )])
    (filter-imm args)))



(define ((uncover-instrs env) instrs)
  (foldr (lambda (instr lvs)
           (cons (set-union (set-subtract (car lvs) (write-locs instr))
                            ((read-locs env) instr))
                 lvs))
         (list (set))
         instrs))

(define ((uncover-block env) block)
  (match block
    [(Block info instrs)
     (Block (dict-set info 'live-vars ((uncover-instrs env) instrs)) instrs)]))

(define (live-vars-in-block block)
  (match block
    [(Block info _)
     (dict-ref info 'live-vars)]))

;; blocks -> directed graph of label
(define (build-control-flow blocks)
  (let ([cfg (make-multigraph '())])
    (begin 
      (for ([(label block) (in-dict blocks)])
         (match block
            [(Block info instrs)
             (begin
               (match (last instrs)
                [(Jmp next-label) #:when (not (equal? next-label 'conclusion))
                 (add-directed-edge! cfg label next-label)]
                [else void])
               (let ([len-of-block (length instrs)])
                   (match (list-ref instrs (- len-of-block 2))
                      [(JmpIf _ next-label) #:when (not (equal? next-label 'conclusion))
                       (add-directed-edge! cfg label next-label)]
                      [else void]
                      )))]))
      cfg)))

(define (sort-uncover-blocks blocks)
  (let ([cfg (build-control-flow blocks)])
    (if (null? (get-vertices cfg))
      (dict-keys blocks)
      (tsort (transpose cfg)))))

;; uncover-live : pseudo-x86 -> pseudo-x86
(define (uncover-live p)
  (match p
    [(X86Program info blocks) 
     (X86Program info (let ([ordered-labels (sort-uncover-blocks blocks)]
                            [label-lives (make-hash)])
                        (cdr (foldl (lambda (label result)
                                       (let* ([label-lives (car result)]
                                             [uncovered-blocks (cdr result)]
                                             [uncovered-block ((uncover-block label-lives) (dict-ref blocks label))])
                                         (cons (dict-set label-lives label (live-vars-in-block uncovered-block))
                                               (dict-set uncovered-blocks label uncovered-block))))
                                    (cons (dict-set '() 'conclusion (list (set (Reg 'rax) (Reg 'rsp))))
                                           '())
                                    ordered-labels))))]))

(define not-equal? (compose1 not equal?))

(define (build-interference-block block init-g)
  (match block
    [(Block info instrs)
     (foldl (lambda (instr lvs interf-graph)
              (match instr
                [(Instr op (list s d)) #:when (member op '(movq movzbq))
                 (let ([s (match op
                            ['movq s]
                            ['movzbq (Reg (byte-reg->full-reg (ByteReg-name s)))])]
                       [vs (filter (lambda (v)
                                     (and (not-equal? v s) (not-equal? v d)))
                                   (set->list lvs))])
                       (begin
                          (for ([v vs])
                              (begin
                                (add-edge! interf-graph v d)))
                          interf-graph))]
                [else (let ([ws (write-locs instr)])
                        (begin
                          (for ([d ws])
                               (for ([v lvs])
                                    (when (not-equal? v d)
                                      (begin
                                        (add-edge! interf-graph v d)))))
                          interf-graph))]))
            init-g
            instrs
            (list-tail (dict-ref info 'live-vars) 1))]))

(define (build-move-graph instrs init-g)
  (foldl (lambda (instr g)
           (match instr
              [(Prim 'movq (list arg1 arg2)) 
               (match (cons arg1 arg2)
                  [(or (cons (Imm _) _) (cons _ (Imm _))) g]
                  [else (begin
                          (add-edge! g arg1 arg2)
                          g)])]
              [else g]))
         init-g
         instrs))



;; build-interference : pseudo-x86 -> pseudo-x86
(define (build-interference p)
  (match p
     [(X86Program info blocks) 
     (X86Program (let ([move-graph (foldl build-move-graph
                                          (apply undirected-graph (list '()))
                                          (map Block-instr* (dict-values blocks)))]
                       [interf-graph (foldl build-interference-block 
                                            (apply undirected-graph (list '())) 
                                            (dict-values blocks))])
                    (begin
                      (display (graphviz interf-graph))
                      (dict-set 
                        (dict-set info 
                          'conflict interf-graph)
                          'move-relation move-graph)))
                 blocks)]))

(define regs '(r15  r11  rbp  rsp  rax  rcx  rdx  rsi  rdi  r8   r9   r10  rbx  r12  r13  r14))

(define reg-num (apply hash (flatten (map cons regs (sequence->list (in-range -4 12))))))


(define num-reg
  (for/hash ([(k v) reg-num])
            (values v k)))

(define (color-graph g move-graph)

  (define (move-colors colored v)
    (if (has-vertex? move-graph v)
        (foldl (lambda (move-var colors)
                 (if (dict-has-key? colored move-var)
                     (cons (dict-ref colored move-var) colors)
                     colors))
               '()
               (get-neighbors move-graph v))
        '()))
  
  (define (available-move-colors saturations colored)
    (lambda (v)
      (filter (compose not negative?) (set->list (set-subtract 
                                                (list->set (move-colors colored v))
                                                (list->set (dict-ref saturations v)))))))

  (define (pick-best-color saturations colored)
    (lambda (v)
      (let ([my-move-colors ((available-move-colors saturations colored) v)])
            (if (null? my-move-colors)
                (let ([sorted (sort (filter (compose not negative?) (dict-ref saturations v)) <)])
                  (foldl (lambda (n minimum)
                           (cond 
                             [(< minimum n) minimum]
                             [(= minimum n) (+ n 1)]
                             [(> minimum n) minimum]
                             ))
                         0
                         sorted))
                (min my-move-colors)))))

  (define (assign-color! saturations)
    (lambda (colored v)
      (match v
        [(Reg r) (dict-set! colored v (hash-ref reg-num r))]
        [(Var name) (dict-set! colored v ((pick-best-color saturations colored) v))]
        [else (error "Unhandled locations")])))

  (define (update-neighbors! v g saturations color)
    (let ([neighbors (get-neighbors g v)])
      (for/list ([neighbor neighbors])
        (dict-set! saturations neighbor (cons color (dict-ref saturations neighbor))))))

  (define (update-priority! queue handles v g)
    (let ([neighbors (get-neighbors g v)])
      (for/list ([neighbor neighbors])
                (pqueue-decrease-key! queue (hash-ref handles v)))))

  (let* ([vertices (get-vertices g)]
        [colored (make-hash)]
        [saturations (let ([d (make-hash)])
                       (begin 
                         (for/list ([v vertices])
                             (dict-set! d v '()))
                         d))]
        [pque (make-pqueue (lambda (lhs rhs)
                              (match (cons lhs rhs)
                                [(cons (Reg _) _)
                                 #t]
                                [(cons _ (Reg _))
                                 #f]
                                [else (let ([lhs-satu-len (length (dict-ref saturations lhs))]
                                            [rhs-satu-len (length (dict-ref saturations rhs))])
                                        (cond
                                          [(> lhs-satu-len rhs-satu-len) #t]
                                          [(< lhs-satu-len rhs-satu-len) #f]
                                          [(= lhs-satu-len rhs-satu-len) (if (null? ((available-move-colors saturations colored) rhs))
                                                                             #t
                                                                             #f)]))])))
              ]
        [item-handles (make-hash)]
        )

    (begin
      (for/list ([v vertices])
        (hash-set! item-handles v (pqueue-push! pque v)))
      (while (not (= (pqueue-count pque) 0))
        (let ([v (pqueue-pop! pque)])
          ((assign-color! saturations) colored v)
          (update-neighbors! v g saturations (dict-ref colored v))
          (update-priority! pque item-handles v g)))
      ;; in case of empty interferecne graph
      (dict-set! colored (Reg 'rax) (hash-ref reg-num 'rax))
      colored)))

(define (num->mem n)
  (let ([num-of-regs (+ (apply max (hash-values reg-num)) 1)])
    (if (< n num-of-regs)
        (Reg (dict-ref num-reg n))
        (Deref 'rbp (* -8 (- n (- num-of-regs 1))))))) 

(define (assign-arg colored)
  (lambda (arg)
    (match arg
      [(or (Reg _) (Var _)) (num->mem (dict-ref colored arg))]
      [(or (Imm _) (ByteReg _)) arg])))

(define (to-full-reg arg)
  (match arg
    [(ByteReg b) (Reg (byte-reg->full-reg b))]
    [else arg]))

(define (assign-homes-instr colored)
  (lambda (instr)
    (match instr
      ;; set instruction has special cc which is not actual argument.
      [(Instr 'set _) instr]
      [(Instr 'movq (list s (Var x))) (if (hash-has-key? colored (Var x))
                                        (Instr 'movq (list ((assign-arg colored) s) ((assign-arg colored) (Var x))))
                                        (Instr 'nop '()))]
      [(Instr name args) (Instr name (map (assign-arg colored) args))]
      [else instr])))

(define (stack-size colored)
  (let ([num-on-stack (let ([num-color (apply max (dict-values colored))])
                        (if (> num-color 10)
                            (- num-color 10)
                            0))])
    (* 8 num-on-stack)))

(define callee-save-regs '(rsp rbp rbx r12 r13 r14 r15))


;; allocate-registers : pseudo-x86 -> pseudo-x86
(define (allocate-registers p)
  (match p
    [(X86Program info blocks) 
     (let ([colored (color-graph (dict-ref info 'conflict) (dict-ref info 'move-relation))])
      (X86Program (dict-set 
                   (dict-set info 'stack-space (stack-size colored))
                   'used-callee
                   (filter (lambda (r)
                             (if (equal? (member r callee-save-regs) #f)
                              #f
                              #t))
                           (map (lambda (num)
                                  (hash-ref num-reg num))
                                (filter (lambda (num)
                                          (if (and (not (negative? num)) (< num 11))
                                            #t
                                            #f))
                                        (dict-values colored)))))
                  (dict-map/copy blocks 
                                 (lambda (label block) 
                                   (values label 
                                           (Block '() (filter (lambda (instr)
                                                                (match instr
                                                                  [(Instr 'nop _) #f]
                                                                  [else #t]))
                                                              (map (assign-homes-instr colored) (Block-instr* block)))))))))]))


(define (patch-instrs instrs)
  (apply append (map (lambda (instr)
                       (match instr
                          [(Instr name (list (Deref 'rbp loc1) (Deref 'rbp loc2)))
                           (list (Instr 'movq (list (Deref 'rbp loc1) (Reg 'rax))) (Instr name (list (Reg 'rax) (Deref 'rbp loc2))))]
                          [(Instr name (list (Imm n) arg))
                            (if (> n 65536)
                             (list (Instr 'movq (list (Imm n) (Reg 'rax))) (Instr name (list (Reg 'rax) arg)))
                             (list instr))]
                          [(Instr 'movq (list arg1 arg2))
                           (if (equal? arg1 arg2)
                             '()
                             (list instr))]
                          [else (list instr)]))
               instrs)))


;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info (list (cons label (Block _ instrs)))) (X86Program info (list (cons label (Block '() (patch-instrs instrs)))))]))

(define (cp-label label)
  (match (system-type 'os)
    ['macosx (string->symbol (string-append "_" (symbol->string label)))]
    [else label]))

(define (aligned-rsp-offset info)
  (let* ([variables-space (dict-ref info 'stack-space)]
         [raw-stack-size (+ variables-space (* 8 (+ 2 (length (dict-ref info 'used-callee)))))])
                                  (if (= (modulo raw-stack-size 16) 8)
                                    (+ 8 variables-space)
                                    variables-space)))


(define (prelude info)
  (append
  (list (Instr 'pushq (list (Reg 'rbp)))
        (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
        (Instr 'subq (list (Imm (aligned-rsp-offset info)) (Reg 'rsp))))
    
  (for/list ([reg (dict-ref info 'used-callee)])
          (Instr 'pushq (list (Reg reg))))
  (list (Jmp (cp-label 'start)))))

(define (conclusion info)
  (append
  (for/list ([reg (reverse (dict-ref info 'used-callee))])
            (Instr 'popq (list (Reg reg))))
  (list (Instr 'addq (list (Imm (aligned-rsp-offset info)) (Reg 'rsp)))
        (Instr 'popq (list (Reg 'rbp)))
        (Retq))))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info (list (cons start (Block _ instrs)))) 
     (X86Program info (list (cons start (Block '() (patch-instrs instrs)))
                            (cons (cp-label 'main) (Block '() (prelude info)))
                            (cons (cp-label 'conclusion) (Block '() (conclusion info)))))]))


     

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes 
  `( ("shrink" ,shrink ,interp-Lif ,type-check-Lif)
  ; `( ("partial evaluator" ,pe-Lint ,interp-Lif ,type-check-Lif)
     ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
     ; ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
     ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-1)
     ("uncover live" ,uncover-live ,interp-pseudo-x86-1)
     ("build interference" ,build-interference ,interp-pseudo-x86-1)
     ("allocate registers" ,allocate-registers ,interp-pseudo-x86-1)
     ; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ; ))
     ))

