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

(define (type-size t) 
  (match t
    ['Integer 8]
    [else (error "unrecognized type" t)]))

(define (var-size v locals-types)
  (type-size (dict-ref locals-types v)))

(define (stack-top locs) 
  (if (dict-empty? locs)
      0
      (apply min (dict-values locs))))

(define (arg-to-stack-loc info)
  (lambda (arg locs)
    (match arg
      [(Var x) 
        (if (dict-has-key? locs x)
            (cons (Deref 'rbp (dict-ref locs x)) locs)
            (let*  ([top (stack-top locs)]
                    [locals-types (dict-ref info 'locals-types)]
                    [s (var-size x locals-types)]
                    [new-top (- top s)])
                        (cons (Deref 'rbp new-top) (dict-set locs x new-top))))]
      [else (cons arg locs)])))


(define (var-to-stack-loc info)
  (lambda (instr locs)
    (let ([to-stack-loc (arg-to-stack-loc info)])
      (match instr
        [(Instr name (list arg)) (let ([arg-locs (to-stack-loc arg locs)]) (cons (Instr name (list (car arg-locs))) (cdr arg-locs)))]
        [(Instr name (list arg1 arg2)) (let* ([arg-locs1 (to-stack-loc arg1 locs)]
                                              [arg-locs2 (to-stack-loc arg2 (cdr arg-locs1))])
                                         (cons (Instr name (list (car arg-locs1) (car arg-locs2))) (cdr arg-locs2)))]
        [else (cons instr locs)]))))


(define (assign-homes-instrs info)
  (lambda (instrs)
    (let ([frame (foldl (lambda (instr acc)
                          (let ([instr-loc ((var-to-stack-loc info) instr (cdr acc))])
                          (cons (append (car acc) (list (car instr-loc))) (cdr instr-loc))))
                        (cons '() '())
                        instrs)])
        (let* ([top (- (stack-top (cdr frame)))]
               [remainder (modulo top 16)])
             (if (= 0 remainder)
                 (cons (car frame) top)
                 (cons (car frame) (+ top (- 16 remainder))))))))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info (list (cons label (Block _ instrs)))) (let ([instrs-loc ((assign-homes-instrs info) instrs)]) 
                                                              (X86Program (dict-set info 'stack-space (cdr instrs-loc)) (list (cons label (Block '() (car instrs-loc))))))]))


(define (patch-instrs instrs)
  (apply append (map (lambda (instr)
                       (match instr
                          [(Instr name (list (Deref 'rbp loc1) (Deref 'rbp loc2)))
                           (list (Instr 'movq (list (Deref 'rbp loc1) (Reg 'rax))) (Instr name (list (Reg 'rax) (Deref 'rbp loc2))))]
                          [(Instr name args)
                            (match args
                              [(list (Imm n) ...)
                                (list (Instr 'movq (list (Imm n) (Reg 'rax))) (Instr name (list (Reg 'rax) (cdr args))))]
                              [else (list (Instr name args))])]
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

(define (prelude info)
  (list (Instr 'pushq (list (Reg 'rbp)))
        (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
        (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
        (Jmp (cp-label 'start))))

(define (conclusion info)
  (list (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
        (Instr 'popq (list (Reg 'rbp)))
        (Retq)))

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
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
