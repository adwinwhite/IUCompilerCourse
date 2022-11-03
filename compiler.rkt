#lang racket
(require graph)
(require racket/set racket/stream)
(require racket/fixnum)
; (require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
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
    [(Let x exp body) (Let x (pe-exp exp) (pe-exp body))]))
    

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
                Prim op (list (Var 'tmp1) (Var 'tmp2)))))])]
      [(Prim 'read '())
       (Prim 'read '())])))



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
    [(Program info e) (CProgram info (dict-set '() (cp-label 'start)  (explicate_tail e)))]))

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
    [(CProgram info (list (cons label tail))) (X86Program info (dict-set '() (cp-label label)  (Block '() (tail->instrs tail))))]))

(define (filter-imm s)
  (list->set (filter (lambda (e)
                       (match e
                         [(Imm _) #f]
                         [else #t]))
                     (set->list s))))

(define (write-locs instr)
  (let ([args (match instr
                [(or (Instr 'subq (list arg1 arg2)) (Instr 'addq (list arg1 arg2)))
                 (set arg2)]
                [(Instr 'negq (list arg1))
                 (set arg1)]
                [(Instr 'movq (list arg1 arg2))
                 (set arg2)]
                [(Instr 'pushq (list arg1))
                 (set)]
                [(Instr 'popq (list arg1))
                 (set arg1)]
                [(Callq label arity)
                 (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
                [Retq
                 (set)]
                [(Jmp label)
                 (set)])])
    (filter-imm args)))


    

(define (read-locs instr)
  (let ([args (match instr
                [(or (Instr 'subq (list arg1 arg2)) (Instr 'addq (list arg1 arg2)))
                 (set arg1 arg2)]
                [(Instr 'negq (list arg1))
                 (set arg1)]
                [(Instr 'movq (list arg1 arg2))
                 (set arg1)]
                [(Instr 'pushq (list arg1))
                 (set arg1)]
                [(Instr 'popq (list arg1))
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
                [Retq
                 (set (Reg 'rax))]
                [(Jmp label)
                 (set)])])
    (filter-imm args)))



(define (uncover-start instrs)
  (foldr (lambda (instr lvs)
           (cons (set-union (set-subtract (car lvs) (write-locs instr))
                            (read-locs instr))
                 lvs))
         (match (last instrs)
           [(Jmp 'conclusion)
            (list (set (Reg 'rax) (Reg 'rsp)))]
           [else (list (set))])
         instrs))


(define (uncover-start-block block)
  (match block
    [(Block info instrs)
     (Block (dict-set info 'live-vars (uncover-start instrs)) instrs)]))

;; uncover-live : pseudo-x86 -> pseudo-x86
(define (uncover-live p)
  (match p
    [(X86Program info blocks) 
     (X86Program info (dict-set blocks (cp-label 'start) (uncover-start-block (dict-ref blocks (cp-label 'start)))))]))

(define not-equal? (compose1 not equal?))

(define (build-interference-block block init)
  (match block
    [(Block info instrs)
     (foldl (lambda (instr lvs interf-graph)
              (match instr
                [(Instr 'movq (list s d))
                 (let ([vs (filter (lambda (v)
                                     (and (not-equal? v s) (not-equal? v d)))
                                   (set->list lvs))])
                       (begin
                          (for ([v vs])
                              (begin
                                (when (not (has-vertex? interf-graph v))
                                      (add-vertex! interf-graph v))
                                (when (not (has-vertex? interf-graph d))
                                      (add-vertex! interf-graph d))
                                (add-edge! interf-graph v d)))
                          interf-graph))]
                [else (let ([ws (write-locs instr)])
                        (begin
                          (for ([d ws])
                               (for ([v lvs])
                                    (when (not-equal? v d)
                                      (begin
                                        (when (not (has-vertex? interf-graph v))
                                              (add-vertex! interf-graph v))
                                        (when (not (has-vertex? interf-graph d))
                                              (add-vertex! interf-graph d))
                                        (add-edge! interf-graph v d)))))
                          interf-graph))]))
            init
            instrs
            (list-tail (dict-ref info 'live-vars) 1))]))


;; build-interference : pseudo-x86 -> pseudo-x86
(define (build-interference p)
  (match p
     [(X86Program info blocks) 
     (X86Program (let ([interf-graph 
                                (foldl build-interference-block (apply undirected-graph (list '())) (map (lambda (label)
                                                                                          (dict-ref blocks label))
                                                                                        (list (cp-label 'start))))])
                    (begin
                      (display (graphviz interf-graph))
                      (dict-set info 'conflict interf-graph)))
                 blocks)]))


(define reg-num #hash((rax . -1)
                       (rsp . -2)
                       (rbp . -3)
                       (r11 . -4)
                       (r15 . -5)
                       (rcx . 0)
                       (rdx . 1)
                       (rsi . 2)
                       (rdi . 3)
                       (r8  . 4)
                       (r9  . 5)
                       (r10 . 6)
                       (rbx . 7)
                       (r12 . 8)
                       (r13 . 9)
                       (r14 . 10)))

(define num-reg
  (for/hash ([(k v) reg-num])
            (values v k)))

(define (color-graph g)
  (define (init-pqueue-cmp lhs rhs)
    (match (cons lhs rhs)
      [(cons (Reg _) _)
       #t]
      [(cons _ (Reg _))
       #f]
      [else #t]))

  (define (minimum-available-num saturation)
    (let ([sorted (sort (filter (compose not negative?) saturation) <)])
      (foldl (lambda (n minimum)
               (if (< minimum n)
                 minimum
                 (+ n 1)))
             0
             sorted)))

  (define (assign-reg! v colored saturation)
    (match v
      [(Reg r) (dict-set! colored v (hash-ref reg-num r))]
      [(Var name) (dict-set! colored v (minimum-available-num saturation))]
      [else (error "Unhandled locations")]))

  (define (update-neighbors! v g saturations color)
    (let ([neighbors (get-neighbors g v)])
      (for/list ([neighbor neighbors])
        (dict-set! saturations neighbor (cons color (dict-ref saturations neighbor))))))

  (let* ([vertices (get-vertices g)]
        [colored (make-hash)]
        [pque (make-pqueue init-pqueue-cmp)]
        [saturations (let ([d (make-hash)])
                       (begin 
                         (for/list ([v vertices])
                             (dict-set! d v '()))
                         d))])

    (begin
      (for/list ([v vertices])
        (pqueue-push! pque v))
      (while (not (= (pqueue-count pque) 0))
        (let ([v (pqueue-pop! pque)])
          (assign-reg! v colored (dict-ref saturations v))
          (update-neighbors! v g saturations (dict-ref colored v))))
      colored)))

(define (num->mem n)
  (if (< n 11)
      (Reg (dict-ref num-reg n))
      (Deref 'rbp (* -8 (- n 10))))) 

(define (assign-arg colored)
  (lambda (arg)
    (match arg
      [(or (Reg _) (Var _)) (num->mem (dict-ref colored arg))]
      [(Imm _) arg])))

(define (assign-homes-instr colored)
  (lambda (instr)
    (match instr
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
    [(X86Program info (list (cons label (Block _ instrs)))) (let ([colored (color-graph (dict-ref info 'conflict))])
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
                                                                          (list (cons label (Block '() (map (assign-homes-instr colored) instrs))))))]))


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
  `( ("partial evaluator" ,pe-Lint ,interp-Lvar ,type-check-Lvar)
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
     ("uncover live" ,uncover-live ,interp-pseudo-x86-0)
     ("build interference" ,build-interference ,interp-pseudo-x86-0)
     ("allocate registers" ,allocate-registers ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
