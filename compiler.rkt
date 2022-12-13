#lang racket
(require graph)
(require data/queue)
(require racket/set
         racket/stream)
(require racket/fixnum)
(require "multigraph.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Cfun.rkt")
(require "interp.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require (prefix-in runtime-config: "runtime-config.rkt"))
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
    [((Int n1) ic2)
     (match ic2
       [(Int n2) (Int (fx+ n1 n2))]
       [(Prim '- (list ire)) (Prim '- (list (Int n1) ire))]
       [(Prim '+ (list (Int n2) ire)) (Prim '+ (list (Int (fx+ n1 n2)) ire))]
       [(Prim '- (list (Int n2) ire)) (Prim '- (list (Int (fx+ n1 n2)) ire))]
       [(Prim '- (list ire (Int n2))) (Prim '+ (list (Int (fx- n1 n2)) ire))]
       [else (Prim '+ (list (Int n1) ic2))])]
    [((Prim '- (list ire1)) ic2)
     (match ic2
       [(Int n1) (Prim '- (list (Int (fx- 0 n1)) ire1))]
       [(Prim '- (list ire2)) (Prim '- (list (Prim '+ (list ire1 ire2))))]
       [(Prim '+ (list (Int n1) ire2)) (Prim '+ (list (Int n1) (Prim '- (list ire2 ire1))))]
       [(Prim '- (list (Int n1) ire2)) (Prim '- (list (Int n1) (Prim '+ (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n1))) (Prim '+ (list (Int (fx- 0 n1)) (Prim '- (list ire2 ire1))))]
       [else (Prim '- (list ic2 ire1))])]
    [((Prim '+ (list (Int n1) ire1)) ic2)
     (match ic2
       [(Int n2) (Prim '+ (list (Int (fx+ n1 n2)) ire1))]
       [(Prim '- (list ire2)) (Prim '+ (list (Int n1) (Prim '- (list ire1 ire2))))]
       [(Prim '+ (list (Int n2) ire2)) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '+ (list ire1 ire2))))]
       [(Prim '- (list (Int n2) ire2)) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '- (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n2))) (Prim '+ (list (Int (fx- n1 n2)) (Prim '+ (list ire1 ire2))))]
       [else (Prim '+ (list (Int n1) (Prim '+ (list ire1 ic2))))])]
    [((Prim '- (list (Int n1) ire1)) ic2)
     (match ic2
       [(Int n2) (Prim '- (list (Int (fx+ n1 n2)) ire1))]
       [(Prim '- (list ire2)) (Prim '- (list (Int n1) (Prim '+ (list ire1 ire2))))]
       [(Prim '+ (list (Int n2) ire2)) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '- (list ire2 ire1))))]
       [(Prim '- (list (Int n2) ire2)) (Prim '- (list (Int (fx+ n1 n2)) (Prim '+ (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n2))) (Prim '+ (list (Int (fx- n1 n2)) (Prim '- (list ire2 ire1))))]
       [else (Prim '+ (list (Int n1) (Prim '- (list ic2 ire1))))])]
    [((Prim '- (list ire1 (Int n1))) ic2)
     (match ic2
       [(Int n2) (Prim '+ (list (Int (fx- n2 n1)) ire1))]
       [(Prim '- (list ire2)) (Prim '+ (list (Int (fx- 0 n1)) (Prim '- (list ire1 ire2))))]
       [(Prim '+ (list (Int n2) ire2)) (Prim '+ (list (Int (fx- n2 n1)) (Prim '+ (list ire1 ire2))))]
       [(Prim '- (list (Int n2) ire2)) (Prim '+ (list (Int (fx- n2 n1)) (Prim '- (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n2))) (Prim '- (list (Prim '+ (list ire1 ire2)) (Int (fx+ n1 n2))))]
       [else (Prim '- (list (Prim '+ (list ire1 ic2)) (Int n1)))])]
    [(ire1 ic2)
     (match ic2
       [(Int n1) (Prim '+ (list (Int n1) ire1))]
       [(Prim '- (list ire2)) (Prim '- (list ire1 ire2))]
       [(Prim '+ (list (Int n1) ire2)) (Prim '+ (list (Int n1) (Prim '+ (list ire1 ire2))))]
       [(Prim '- (list (Int n1) ire2)) (Prim '+ (list (Int n1) (Prim '- (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n1))) (Prim '- (list (Prim '+ (list ire1 ire2)) (Int n1)))]
       [else (Prim '+ (list ire1 ic2))])]))

(define (pe-sub ic1 ic2)
  (match* (ic1 ic2)
    [((Int n1) ic2)
     (match ic2
       [(Int n2) (Int (fx- n1 n2))]
       [(Prim '- (list ire)) (Prim '+ (list (Int n1) ire))]
       [(Prim '+ (list (Int n2) ire)) (Prim '- (list (Int (fx- n1 n2)) ire))]
       [(Prim '- (list (Int n2) ire)) (Prim '+ (list (Int (fx- n1 n2)) ire))]
       [(Prim '- (list ire (Int n2))) (Prim '- (list (Int (fx+ n1 n2)) ire))]
       [else (Prim '- (list (Int n1) ic2))])]
    [((Prim '- (list ire1)) ic2)
     (match ic2
       [(Int n1) (Prim '- (list (Int (fx- 0 n1)) ire1))]
       [(Prim '- (list ire2)) (Prim '- (list ire2 ire1))]
       [(Prim '+ (list (Int n1) ire2)) (Prim '- (list (Int (fx- 0 n1)) (Prim '+ (list ire2 ire1))))]
       [(Prim '- (list (Int n1) ire2)) (Prim '- (list (Int (fx- 0 n1)) (Prim '- (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n1))) (Prim '- (list (Int n1) (Prim '+ (list ire2 ire1))))]
       [else (Prim '- (list (Prim '+ (list (ic2 ire1)))))])]
    [((Prim '+ (list (Int n1) ire1)) ic2)
     (match ic2
       [(Int n2) (Prim '+ (list (Int (fx- n1 n2)) ire1))]
       [(Prim '- (list ire2)) (Prim '+ (list (Int n1) (Prim '+ (list ire1 ire2))))]
       [(Prim '+ (list (Int n2) ire2)) (Prim '+ (list (Int (fx- n1 n2)) (Prim '- (list ire1 ire2))))]
       [(Prim '- (list (Int n2) ire2)) (Prim '+ (list (Int (fx- n1 n2)) (Prim '+ (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n2))) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '- (list ire1 ire2))))]
       [else (Prim '+ (list (Int n1) (Prim '- (list ire1 ic2))))])]
    [((Prim '- (list (Int n1) ire1)) ic2)
     (match ic2
       [(Int n2) (Prim '- (list (Int (fx- n1 n2)) ire1))]
       [(Prim '- (list ire2)) (Prim '+ (list (Int n1) (Prim '- (list ire2 ire1))))]
       [(Prim '+ (list (Int n2) ire2)) (Prim '- (list (Int (fx- n1 n2)) (Prim '+ (list ire2 ire1))))]
       [(Prim '- (list (Int n2) ire2)) (Prim '- (list (Int (fx- n1 n2)) (Prim '- (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n2))) (Prim '- (list (Int (fx+ n1 n2)) (Prim '+ (list ire2 ire1))))]
       [else (Prim '- (list (Int n1) (Prim '+ (list ic2 ire1))))])]
    [((Prim '- (list ire1 (Int n1))) ic2)
     (match ic2
       [(Int n2) (Prim '- (list ire1 (Int (fx+ n2 n1))))]
       [(Prim '- (list ire2)) (Prim '- (list (Prim '+ (list ire1 ire2)) (Int n1)))]
       [(Prim '+ (list (Int n2) ire2)) (Prim '- (list (Prim '- (list ire1 ire2)) (Int (fx+ n1 n2))))]
       [(Prim '- (list (Int n2) ire2)) (Prim '- (list (Prim '+ (list ire1 ire2)) (Int (fx+ n1 n2))))]
       [(Prim '- (list ire2 (Int n2))) (Prim '+ (list (Int (fx- n2 n1)) (Prim '- (list ire1 ire2))))]
       [else (Prim '+ (list (Int (fx- 0 n1)) (Prim '- (list ire1 ic2))))])]
    [(ire1 ic2)
     (match ic2
       [(Int n1) (Prim '- (list ire1 (Int n1)))]
       [(Prim '- (list ire2)) (Prim '+ (list ire1 ire2))]
       [(Prim '+ (list (Int n1) ire2)) (Prim '+ (list (Int (fx- 0 n1)) (Prim '- (list ire1 ire2))))]
       [(Prim '- (list (Int n1) ire2)) (Prim '+ (list (Int (fx- 0 n1)) (Prim '+ (list ire1 ire2))))]
       [(Prim '- (list ire2 (Int n1))) (Prim '+ (list (Int n1) (Prim '- (list ire1 ire2))))]
       [else (Prim '- (list ire1 ic2))])]))

(define cmp-op '(eq? < <= > >=))

(define cmp-proc (list eq? < <= > >=))

(define cmp-set '(sete setl setle setg setge))

(define cmp-cc '(e l le g ge))

(define cmp-jmp '(je jl jle jg jge))

(define cmp-op-proc (map cons cmp-op cmp-proc))

(define cmp-op-set (map cons cmp-op cmp-set))

(define cmp-op-jmp (map cons cmp-op cmp-jmp))

(define cmp-op-cc (map cons cmp-op cmp-cc))

(define (pe-cmp op e1 e2)
  (match* (e1 e2)
    [((Int n1) (Int n2)) (Bool ((dict-ref cmp-op-proc op) n1 n2))]
    [((Bool b1) (Bool b2))
     #:when (equal? op 'eq?)
     (Bool ((dict-ref cmp-op-proc op) b1 b2))]
    [(_ _) (Prim op (list e1 e2))]))

(define (pe-if cnd thn els)
  (match cnd
    [(Bool b) (if b thn els)]
    [else (If cnd thn els)]))

;; Only returns (+ n x) or (- x n) or (- n x). neg -> sub.
(define (pe-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void)
     (begin
       (println e)
       Void)]
    [(SetBang var exp) (SetBang var (pe-exp exp))]
    [(Begin es body) (Begin (map pe-exp es) (pe-exp body))]
    [(WhileLoop cnd body) (WhileLoop (pe-exp cnd) (pe-exp body))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))]
    [(Prim op (list e1 e2))
     #:when (member op cmp-op)
     (pe-cmp op (pe-exp e1) (pe-exp e2))]
    [(Let x exp body) (Let x (pe-exp exp) (pe-exp body))]
    [(If cnd thn els) (pe-if (pe-exp cnd) (pe-exp thn) (pe-exp els))]
    [else e]))

(define (pe-Lfun p)
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
    [(ProgramDefsExp info defs e)
     (ProgramDefs info (cons (Def 'main '() 'Integer '() (shrink-logical e)) defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define ((uniquify-name env) x)
  (gensym x))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Void) (Void)]
      [(Let x e body)
       (let* ([unique-name ((uniquify-name env) x)] [new-env (dict-set env x unique-name)])
         (Let unique-name ((uniquify-exp new-env) e) ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op
             (for/list ([e es])
               ((uniquify-exp env) e)))]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [(SetBang var exp) (SetBang (dict-ref env var) ((uniquify-exp env) exp))]
      [(Begin es body) (Begin (map (uniquify-exp env) es) ((uniquify-exp env) body))]
      [(WhileLoop cnd body) (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(HasType exp t) (HasType ((uniquify-exp env) exp) t)]
      [(Apply f args) (Apply ((uniquify-exp env) f) (map (uniquify-exp env) args))])))

(define (param->pair p)
  (match p
    [`(,x : ,t) (values x t)]))

(define (pair->param x t)
  `(,x : ,t))

(define ((uniquify-params env) params)
  (foldl (lambda (p new-env)
           (define-values (x t) (param->pair p))
           (dict-set new-env x ((uniquify-name new-env) x)))
         env
         params))

(define ((uniquify-def env) def)
  (match def
    [(Def name params rt info body)
     (define unique-env-mapping ((uniquify-params env) params))
     (Def name
          (for/list ([p params])
            (define-values (x t) (param->pair p))
            (pair->param (dict-ref unique-env-mapping x) t))
          rt
          info
          ((uniquify-exp unique-env-mapping) body))]))

(define (extract-func-name defs)
  (map Def-name defs))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(ProgramDefs info defs)
     (define func-names (extract-func-name defs))
     (define func-name-dict (map (lambda (n) (cons n n)) func-names))
     (ProgramDefs info (map (uniquify-def func-name-dict) defs))]))

(define (gentmp)
  (gensym 'tmp))

;; tmps: temporary variables that are bound to expressions.
;; es: remaining expressions to bind.
(define ((create-vector tmps types) es)
  (if (null? es)
      (let ([bytes (* 8 (+ 1 (length tmps)))])
        (Begin (list (If (Prim '<
                               (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes)))
                                     (GlobalValue 'fromspace_end)))
                         (Void)
                         (Collect bytes)))
               (let ([tmpvec (gensym 'vec)])
                 (Let tmpvec
                      (Allocate (length tmps) types)
                      (Begin (for/list ([tmp (reverse tmps)] [index (in-naturals)])
                               (Prim 'vector-set! (list (Var tmpvec) (Int index) (Var tmp))))
                             (Var tmpvec))))))
      (let ([tmp (gentmp)] [head (car es)])
        (Let tmp head ((create-vector (cons tmp tmps) types) (cdr es))))))

(define (expose-allocation-exp exp)
  (match exp
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x e body) (Let x (expose-allocation-exp e) (expose-allocation-exp body))]
    [(Prim op es)
     (Prim op
           (for/list ([e es])
             (expose-allocation-exp e)))]
    [(If cnd thn els)
     (If (expose-allocation-exp cnd) (expose-allocation-exp thn) (expose-allocation-exp els))]
    [(SetBang var exp) (SetBang var (expose-allocation-exp exp))]
    [(Begin es body) (Begin (map expose-allocation-exp es) (expose-allocation-exp body))]
    [(WhileLoop cnd body) (WhileLoop (expose-allocation-exp cnd) (expose-allocation-exp body))]
    [(HasType (Prim 'vector es) ts) ((create-vector '() ts) (map expose-allocation-exp es))]))

;; expose-allocation : Lfun -> Lfun
(define (expose-allocation p)
  (match p
    [(Program info e) (Program info (expose-allocation-exp e))]))

(define (collect-setbang e)
  (match e
    [(Var x) (set)]
    [(Int n) (set)]
    [(Bool b) (set)]
    [(Void) (set)]
    [(Let x exp body) (set-union (collect-setbang exp) (collect-setbang body))]
    [(Prim op es) (if (eq? (length es) 0) (set) (apply set-union (map collect-setbang es)))]
    [(If cnd thn els) (set-union (collect-setbang cnd) (collect-setbang thn) (collect-setbang els))]
    [(SetBang var exp) (set-union (set var) (collect-setbang exp))]
    [(Begin es body) (set-union (apply set-union (map collect-setbang es)) (collect-setbang body))]
    [(WhileLoop cnd body) (set-union (collect-setbang cnd) (collect-setbang body))]
    [else (set)]))

(define ((uncover-get-exp mutable-vars) e)
  (define (mut->getbang x)
    (if (set-member? mutable-vars x) (GetBang x) (Var x)))
  (match e
    [(Var x) (mut->getbang x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x exp body)
     (Let x ((uncover-get-exp mutable-vars) exp) ((uncover-get-exp mutable-vars) body))]
    [(Prim op es) (Prim op (map (uncover-get-exp mutable-vars) es))]
    [(If cnd thn els)
     (If ((uncover-get-exp mutable-vars) cnd)
         ((uncover-get-exp mutable-vars) thn)
         ((uncover-get-exp mutable-vars) els))]
    [(SetBang var exp) (SetBang var ((uncover-get-exp mutable-vars) exp))]
    [(Begin es body)
     (Begin (map (uncover-get-exp mutable-vars) es) ((uncover-get-exp mutable-vars) body))]
    [(WhileLoop cnd body)
     (WhileLoop ((uncover-get-exp mutable-vars) cnd) ((uncover-get-exp mutable-vars) body))]
    [else e]))

;; uncover-get!: Lwhile->Lwhile
(define (uncover-getbang p)
  (match p
    [(Program info e) (Program info ((uncover-get-exp (collect-setbang e)) e))]))

(define remove-complex-opera-exp
  (lambda (e)
    (match e
      [(GetBang x) (Var x)]
      [(Let x e body) (Let x (remove-complex-opera-exp e) (remove-complex-opera-exp body))]
      [(Prim op (list e))
       (if (atm? e)
           (Prim op (list e))
           (let ([tmp (gentmp)]) (Let tmp (remove-complex-opera-exp e) (Prim op (list (Var tmp))))))]
      [(Prim op (list e1 e2))
       (match (cons (atm? e1) (atm? e2))
         [(cons #t #t) (Prim op (list e1 e2))]
         [(cons #t #f)
          (let ([tmp (gentmp)])
            (Let tmp (remove-complex-opera-exp e2) (Prim op (list e1 (Var tmp)))))]
         [(cons #f #t)
          (let ([tmp (gentmp)])
            (Let tmp (remove-complex-opera-exp e1) (Prim op (list (Var tmp) e2))))]
         [(cons #f #f)
          (let ([tmp1 (gentmp)] [tmp2 (gentmp)])
            (Let tmp1
                 (remove-complex-opera-exp e1)
                 (Let tmp2 (remove-complex-opera-exp e2) (Prim op (list (Var tmp1) (Var tmp2))))))])]
      ;; TODO: got optimized later?
      [(Prim 'vector-set! (list e1 (Int i) e2))
       (let ([tmpvec (gentmp)] [tmpexp (gentmp)])
         (Let tmpvec
              (remove-complex-opera-exp e1)
              (Let tmpexp
                   (remove-complex-opera-exp e2)
                   (Prim 'vector-set! (list (Var tmpvec) (Int i) (Var tmpexp))))))]
      [(If cnd thn els)
       (If (remove-complex-opera-exp cnd)
           (remove-complex-opera-exp thn)
           (remove-complex-opera-exp els))]
      [(SetBang var exp)
       (if (atm? exp)
           e
           (let ([tmp (gentmp)]) (Let tmp (remove-complex-opera-exp exp) (SetBang var (Var tmp)))))]
      [(Begin es body) (Begin (map remove-complex-opera-exp es) (remove-complex-opera-exp body))]
      [(WhileLoop cnd body)
       (WhileLoop (remove-complex-opera-exp cnd) (remove-complex-opera-exp body))]
      [else e])))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (remove-complex-opera-exp e))]))

;; whether the expression has side effect
;; do I write this expression for its side effect?
(define (pure-exp? e)
  (match e
    [(Var x) #t]
    [(Int n) #t]
    [(Bool b) #t]
    [(Void) #t]
    [(Let x exp body) (and (pure-exp? exp) (pure-exp? body))]
    [(Prim 'vector-set! es) #f]
    [(Prim op es) (andmap pure-exp? es)]
    [(If cnd thn els) (and (pure-exp? cnd) (pure-exp? thn) (pure-exp? els))]
    [(SetBang var exp) #f]
    [(Begin es body) (and (andmap pure-exp? es) (pure-exp? body))]
    [(WhileLoop cnd body) (and (pure-exp? cnd) (pure-exp? body))]
    [(Allocate n ts) #t]
    [(GlobalValue var) #t]
    [(Collect bytes) #f]))

;; create a new block with the instructions of tail.
;; return a single instruction `Goto label` where `label` points to the block just created.
(define ((create-block blocks) tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
     (let ([label (gensym 'block)])
       (dict-set! blocks label tail)
       (Goto label))]))

;; (predicate, effect expression, tail) -> tail
(define ((explicate-while blocks) cnd body cont)
  (let ([loop-label (gensym 'loop)] [body-label (gensym 'body)] [cont-label (gensym 'block)])
    (dict-set! blocks cont-label cont)
    (dict-set! blocks body-label ((explicate-effect blocks) body (Goto loop-label)))
    (dict-set! blocks loop-label ((explicate-pred blocks) cnd (Goto body-label) (Goto cont-label)))
    (Goto loop-label)))

;; Only e and cont are delayed.
(define (explicate-assign blocks)
  (lambda (e x cont)
    (match e
      [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
      [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
      [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
      [(Void) (Seq (Assign (Var x) (Void)) cont)]
      [(Let y rhs body) ((explicate-assign blocks) rhs y ((explicate-assign blocks) body x cont))]
      [(SetBang var atm) (Seq (Assign (Var var) atm) (Seq (Assign (Var x) (Void)) cont))]
      [(Begin es body) ((explicate-begin blocks) es ((explicate-assign blocks) body x cont))]
      [(WhileLoop cnd body) ((explicate-while blocks) cnd body (Seq (Assign (Var x) (Void)) cont))]
      [(If cnd thn els)
       (let ([goto-cont ((create-block blocks) cont)])
         ((explicate-pred blocks) cnd
                                  ((explicate-assign blocks) thn x goto-cont)
                                  ((explicate-assign blocks) els x goto-cont)))]
      [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
      [(Allocate n ts) (Seq (Assign (Var x) (Allocate n ts)) cont)]
      [(GlobalValue var) (Seq (Assign (Var x) (GlobalValue var)) cont)]
      [else (error "explicate-assign unhandled case" e)])))

;; exp -> tail
(define (explicate-tail blocks)
  (lambda (e)
    (match e
      [(Var x) (Return (Var x))]
      [(Int n) (Return (Int n))]
      [(Bool b) (Return (Bool b))]
      [(Void) (Return (Void))]
      [(SetBang var atm) ((explicate-assign blocks) atm var (Return (Void)))]
      [(Begin es body) ((explicate-begin blocks) es ((explicate-tail blocks) body))]
      [(WhileLoop cnd body) ((explicate-while blocks) cnd body (Return (Void)))]
      [(Let x rhs body) ((explicate-assign blocks) rhs x ((explicate-tail blocks) body))]
      [(If cnd thn els)
       ((explicate-pred blocks) cnd ((explicate-tail blocks) thn) ((explicate-tail blocks) els))]
      [(Prim op atms) (Return (Prim op atms))]
      [else (error "explicate-tail unhandled case" e)])))

;; (exp-bool, tail, tail) -> tail
(define (explicate-pred blocks)
  (lambda (cnd thn els)
    (match cnd
      [(Var x)
       (IfStmt (Prim 'eq? (list (Var x) (Bool #t)))
               (force ((create-block blocks) thn))
               (force ((create-block blocks) els)))]
      [(Let x rhs body) ((explicate-assign blocks) rhs x ((explicate-pred blocks) body thn els))]
      [(Prim 'not (list e)) ((explicate-pred blocks) e els thn)]
      [(Prim op es)
       #:when (member op cmp-op)
       (IfStmt (Prim op es) (force ((create-block blocks) thn)) (force ((create-block blocks) els)))]
      [(Prim 'vector-ref (list vec (Int i)))
       (let ([tmp (gentmp)])
         ((explicate-assign blocks) cnd tmp ((explicate-pred blocks) (Var tmp) thn els)))]
      [(Bool b) (if b thn els)]
      [(If cnd-inn thn-inn els-inn)
       (let ([outer-thn ((create-block blocks) thn)] [outer-els ((create-block blocks) els)])
         ((explicate-pred blocks) cnd-inn
                                  ((explicate-pred blocks) thn-inn outer-thn outer-els)
                                  ((explicate-pred blocks) els-inn outer-thn outer-els)))]
      [(Begin es body) ((explicate-begin blocks) es ((explicate-pred blocks) body thn els))]
      [else (error "explicate-pred unhandled case" cnd)])))

;; TODO: we can filter out expression that doesn't change outside variables.
;; (exp-effect, tail) -> tail
(define ((explicate-effect blocks) effect cont)
  (if (pure-exp? effect)
      cont
      (match effect
        [(SetBang var atm) (Seq (Assign (Var var) atm) cont)]
        [(Begin es body) ((explicate-begin blocks) es ((explicate-effect blocks) body cont))]
        [(WhileLoop cnd body) ((explicate-while blocks) cnd body cont)]
        [(Let x rhs body) ((explicate-assign blocks) rhs x ((explicate-effect blocks) body cont))]
        [(If cnd thn els)
         (let ([goto-cont ((create-block blocks) cont)])
           ((explicate-pred blocks) cnd
                                    ((explicate-effect blocks) thn goto-cont)
                                    ((explicate-effect blocks) els goto-cont)))]
        [(Prim 'vector-set! _) (Seq effect cont)]
        [(Collect _) (Seq effect cont)]
        [else (error "explicate-tail unhandled case" effect)])))

(define ((explicate-begin blocks) es cont)
  (foldl (explicate-effect blocks) cont (reverse es)))

;; explicate-control : Lwhile^atm -> Cwhile
(define (explicate-control p)
  (match p
    [(Program info e)
     (CProgram info
               (let ([basic-blocks (make-hash)])
                 (begin
                   (dict-set! basic-blocks (cp-label 'start) ((explicate-tail basic-blocks) e))
                   basic-blocks)))]))

(define (atm->args a)
  (match a
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    [(Bool b) (if b (Imm 1) (Imm 0))]
    [(Void) (Imm 0)]
    [else (error "not atm" a)]))

(define (pointer? t)
  (match t
    [`(Vector ,@(list _ ...)) #t]
    ['Integer #f]
    ['Boolean #f]
    ['Void #f]
    [else (error "unhandled type ~a by pointer?" t)]))

(define (generate-pointer-mask ts)
  (foldl (lambda (t n)
           (let ([shifted (arithmetic-shift n 1)]) (if (pointer? t) (bitwise-ior shifted 1) shifted)))
         0
         ts))

(define (generate-tag ts)
  (let* ([ts (cdr ts)] [len (length ts)])
    (arithmetic-shift (bitwise-ior (arithmetic-shift (generate-pointer-mask ts) 6) len) 1)))

(define (stmt->instrs s)
  (match s
    [(Assign x exp)
     (match exp
       [(? atm?) (list (Instr 'movq (list (atm->args exp) x)))]
       [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
       [(Prim '- (list e))
        (if (equal? e x)
            (list (Instr 'negq (list x)))
            (list (Instr 'movq (list (atm->args e) x)) (Instr 'negq (list x))))]
       [(Prim '+ (list e1 e2))
        (cond
          [(equal? e1 x) (list (Instr 'addq (list (atm->args e2) x)))]
          [(equal? e2 x) (list (Instr 'addq (list (atm->args e1) x)))]
          [else (list (Instr 'movq (list (atm->args e1) x)) (Instr 'addq (list (atm->args e2) x)))])]
       [(Prim '- (list e1 e2))
        (if (equal? e1 x)
            (list (Instr 'subq (list (atm->args e2) x)))
            (list (Instr 'movq (list (atm->args e1) x)) (Instr 'subq (list (atm->args e2) x))))]
       [(Prim 'not (list e))
        (if (equal? e x)
            (list (Instr 'xorq (list (Imm 1) x)))
            (list (Instr 'movq (list (atm->args e) x)) (Instr 'xorq (list (Imm 1) x))))]
       [(Prim op (list e1 e2))
        #:when (member op cmp-op)
        (list (Instr 'cmpq (list (atm->args e2) (atm->args e1)))
              (Instr 'set (list (dict-ref cmp-op-cc op) (ByteReg 'al)))
              (Instr 'movzbq (list (ByteReg 'al) x)))]
       [(Prim 'vector-ref (list vec (Int i)))
        (list (Instr 'movq (list vec (Reg 'r11))) (Instr 'movq (list (Deref 'r11 (* 8 (+ i 1))) x)))]
       [(Prim 'vector-set! (list vec (Int i) atm))
        (list (Instr 'movq (list vec (Reg 'r11)))
              (Instr 'movq (list atm (Deref 'r11 (* 8 (+ i 1)))))
              (Instr 'movq (list (Imm 0) x)))]
       [(Prim 'vector-length (list vec))
        (list (Instr 'movq (list vec (Reg 'r11)))
              (Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
              (Instr 'sarq (list (Imm 1) (Reg 'rax)))
              (Instr 'andq (list (Imm #b111111) (Reg 'rax)))
              (Instr 'movq (list (Reg 'rax) x)))]
       ;; If we really want to support 50-length, we need to use movabsq rather than movq.
       [(Allocate n ts)
        (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
              (Instr 'addq (list (Imm (* 8 (+ n 1))) (Global 'free_ptr)))
              (Instr 'movq (list (Imm (generate-tag ts)) (Deref 'r11 0)))
              (Instr 'movq (list (Reg 'r11) x)))]
       [(GlobalValue var) (list (Instr 'movq (list (Global var) x)))]
       [else (error "unhandled expression in assignment statement" exp)])]
    [(Prim 'read '()) (list (Callq 'read_int 0))]
    [(Prim 'vector-set! (list vec (Int i) atm))
     (list (Instr 'movq (list vec (Reg 'r11))) (Instr 'movq (list atm (Deref 'r11 (* 8 (+ i 1))))))]
    [(Collect bytes)
     (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
           (Instr 'movq (list (Imm bytes) (Reg 'rsi)))
           (Callq 'collect 0))]
    [else (error "stmt->instrs unhandled statements" s)]))

(define (tail->instrs t)
  (match t
    [(Return e) (append (stmt->instrs (Assign (Reg 'rax) e)) (list (Jmp 'conclusion)))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim op (list e1 e2)) (Goto label1) (Goto label2))
     (list (Instr 'cmpq (list (atm->args e2) (atm->args e1)))
           (JmpIf (dict-ref cmp-op-cc op) label1)
           (Jmp label2))]
    [(Seq fst snd) (append (stmt->instrs fst) (tail->instrs snd))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info blocks)
     (X86Program
      info
      (dict-map/copy blocks (lambda (label tail) (values label (Block '() (tail->instrs tail))))))]))

(define (filter-static s)
  (list->set (filter (lambda (e)
                       (match e
                         [(Imm _) #f]
                         ; [(Global _) #f]
                         ; [(Deref r o) #f]
                         [else #t]))
                     (set->list s))))

(define (write-locs instr)
  (let ([args (match instr
                [(Instr op (list arg1 arg2))
                 #:when (member op '(subq addq xorq movq movzbq))
                 (set arg2)]
                [(Instr 'negq (list arg1)) (set arg1)]
                [(Instr 'pushq (list arg1)) (set)]
                [(Instr 'cmpq (list arg1 arg2)) (set)]
                [(Instr 'set (list cc arg1)) (set (Reg (byte-reg->full-reg (ByteReg-name arg1))))]
                [(Instr 'popq (list arg1)) (set arg1)]
                [(Callq label arity)
                 (set (Reg 'rax)
                      (Reg 'rcx)
                      (Reg 'rdx)
                      (Reg 'rsi)
                      (Reg 'rdi)
                      (Reg 'r8)
                      (Reg 'r9)
                      (Reg 'r10)
                      (Reg 'r11))]
                [Retq (set)]
                [(or (Jmp label) (JmpIf _ label)) (set)])])
    (filter-static args)))

(define (read-locs instr)
  (let ([args (match instr
                [(Instr op (list arg1 arg2))
                 #:when (member op '(subq addq xorq cmpq))
                 (set arg1 arg2)]
                [(Instr 'negq (list arg1)) (set arg1)]
                [(Instr 'movq (list arg1 arg2)) (set arg1)]
                [(Instr 'movzbq (list arg1 arg2))
                 (set (Reg (byte-reg->full-reg (ByteReg-name arg1))))]
                [(Instr 'pushq (list arg1)) (set arg1)]
                [(Instr 'popq (list arg1)) (set)]
                [(Instr 'set (list cc arg1)) (set)]
                [(Callq label arity)
                 (match arity
                   [0 (set)]
                   [1 (set (Reg 'rdi))]
                   [2 (set (Reg 'rdi) (Reg 'rsi))]
                   [3 (set (Reg 'rdi) (Reg 'rsi) (Reg 'rdx))]
                   [4 (set (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx))]
                   [5 (set (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8))]
                   [6 (set (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9))]
                   [n
                    (list->set (map (lambda (x)
                                      Deref
                                      'rbp
                                      (+ 16 (* 8 x)))
                                    (stream->list (in-range (- n 6)))))])]
                [(struct Retq _) (set (Reg 'rax))]
                [(or (Jmp label) (JmpIf _ label)) (set)])])
    (filter-static args)))

(define (uncover-instrs instrs live-after)
  (foldr (lambda (instr lvs)
           (cons (set-union (set-subtract (car lvs) (write-locs instr)) (read-locs instr)) lvs))
         (list live-after)
         instrs))

(define ((uncover-label blocks) label live-after)
  (if (equal? label 'conclusion)
      (set (Reg 'rsp) (Reg 'rax))
      (car (uncover-instrs (Block-instr* (dict-ref blocks label)) live-after))))

(define (uncover-block label block live-after)
  (match block
    [(Block info instrs)
     (Block (dict-set info 'live-vars (uncover-instrs instrs live-after)) instrs)]))

(define (live-vars-in-block block)
  (match block
    [(Block info _) (dict-ref info 'live-vars)]))

;; TODO: filter out unused blocks(no other block pointing to).
;; blocks -> directed graph of label
(define (build-control-flow blocks)
  (let ([cfg (make-multigraph '())])
    (begin
      (for ([(label block) (in-dict blocks)])
        (match block
          [(Block info instrs)
           (begin
             (match (last instrs)
               [(Jmp next-label) (add-directed-edge! cfg label next-label)]
               [else void])
             (let ([len-of-block (length instrs)])
               (match (list-ref instrs (- len-of-block 2))
                 [(JmpIf _ next-label) (add-directed-edge! cfg label next-label)]
                 [else void])))]))
      cfg)))

;; multigraph has a bug that vertices not pointed to are ignored.
;; mapping: {label->live-before set}
(define (analyze_dataflow G transfer bottom join)
  (define mapping (make-hash))
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input
           (for/fold ([state bottom]) ([pred (in-neighbors trans-G node)])
             (join state (dict-ref mapping pred))))
         (define output (transfer node input))
         (cond
           [(not (equal? output (dict-ref mapping node)))
            (dict-set! mapping node output)
            (for ([v (in-neighbors G node)])
              (enqueue! worklist v))]))
  mapping)

(define ((uncover-bottom live-befores control-flow-graph) label)
  (foldl set-union
         (set)
         (map (lambda (next-label) (dict-ref live-befores next-label))
              (get-neighbors control-flow-graph label))))

;; uncover-live : pseudo-x86 -> pseudo-x86
(define (uncover-live p)
  (match p
    [(X86Program info blocks)
     (let* ([cfg (build-control-flow blocks)]
            [live-befores (analyze_dataflow (transpose cfg) (uncover-label blocks) (set) set-union)]
            [live-afters (foldl (lambda (label las)
                                  (dict-set las label ((uncover-bottom live-befores cfg) label)))
                                '()
                                (get-vertices cfg))])
       (X86Program
        (dict-set info 'control-flow-graph cfg)
        (foldl
         (lambda (label bs)
           (dict-set bs
                     label
                     (uncover-block label (dict-ref blocks label) (dict-ref live-afters label))))
         '()
         (get-vertices cfg))))]))

(define not-equal? (compose1 not equal?))

(define ((heap-var? types) v)
  (match v
    [(Var x)
     (let ([t (dict-ref types x)])
       (match t
         [`(Vector ...) #t]
         ['Vector #t]
         [else #f]))]
    [else #f]))

(define (interferes-callee-regs v g)
  (for ([r callee-save])
    (when (not-equal? r v)
      (add-edge! g v r))))

(define ((build-interference-block types) block init-g-and-lives)
  (match block
    [(Block info instrs)
     (foldl
      (lambda (instr lvs acc)
        (let ([interf-graph (car acc)] [call-live-heap-vars (cdr acc)])
          (match instr
            [(Instr op (list s d))
             #:when (member op '(movq movzbq))
             (let ([s (match op
                        ['movq s]
                        ['movzbq (Reg (byte-reg->full-reg (ByteReg-name s)))])]
                   [vs (filter (lambda (v) (and (not-equal? v s) (not-equal? v d))) (set->list lvs))])
               (begin
                 (for ([v vs])
                   (begin
                     (add-edge! interf-graph v d)))
                 (cons interf-graph call-live-heap-vars)))]
            [else
             (let ([ws (write-locs instr)])
               (begin
                 (for ([d ws])
                   (for ([v lvs])
                     (when (not-equal? v d)
                       (begin
                         (add-edge! interf-graph v d)))))
                 (match instr
                   [(Callq 'collect 0)
                    (let ([heap-lvs (filter (heap-var? types) (set->list lvs))])
                      (for ([v heap-lvs])
                        (begin
                          (set-add! call-live-heap-vars v)
                          (interferes-callee-regs v interf-graph))))]
                   [else void])
                 (cons interf-graph call-live-heap-vars)))])))
      init-g-and-lives
      instrs
      (list-tail (dict-ref info 'live-vars) 1))]))

(define (build-move-graph instrs init-g)
  (foldl (lambda (instr g)
           (match instr
             [(Prim 'movq (list arg1 arg2))
              (match (cons arg1 arg2)
                [(or (cons (Imm _) _) (cons _ (Imm _))) g]
                [else
                 (begin
                   (add-edge! g arg1 arg2)
                   g)])]
             [else g]))
         init-g
         instrs))

;; build-interference : pseudo-x86 -> pseudo-x86
(define (build-interference p)
  (match p
    [(X86Program info blocks)
     (X86Program
      (let* ([move-graph (foldl build-move-graph
                                (apply undirected-graph (list '()))
                                (map Block-instr* (dict-values blocks)))]
             [interf-graph-and-call-lives
              (foldl (build-interference-block (dict-ref info 'locals-types))
                     (cons (apply undirected-graph (list '())) (set))
                     (dict-values blocks))]
             [interf-graph (car interf-graph-and-call-lives)]
             [call-live-heap-vars (cdr interf-graph-and-call-lives)])
        (begin
          (display (graphviz interf-graph))
          (dict-set (dict-set (dict-set info 'conflict interf-graph) 'move-relation move-graph)
                    'root-vars
                    call-live-heap-vars)))
      blocks)]))

; Do I need to keep rax at num=0?
(define regs '(r15 r11 rbp rsp rax rcx rdx rsi rdi r8 r9 r10 rbx r12 r13 r14))

; Now I see why it's ordered like this.
; r15 and r11 have special uses.
(define reg-num-start -4)

(define number-of-reg-alloc (length regs))

(define reg-num-end (+ reg-num-start number-of-reg-alloc))

(define reg-num
  (apply hash (flatten (map cons regs (sequence->list (in-range reg-num-start reg-num-end))))))

(define num-reg
  (for/hash ([(k v) reg-num])
    (values v k)))

(define (mem-location? v)
  (match v
    [(Global _) #t]
    [(Deref _ _) #t]
    [else #f]))

(define (color-graph g move-graph root-vars)

  (define (move-colors colored v)
    (if (has-vertex? move-graph v)
        (foldl
         (lambda (move-var colors)
           (if (dict-has-key? colored move-var) (cons (dict-ref colored move-var) colors) colors))
         '()
         (get-neighbors move-graph v))
        '()))

  (define (available-move-colors saturations colored)
    (lambda (v)
      (set->list (set-subtract (list->set (move-colors colored v))
                               (list->set (dict-ref saturations v))))))

  (define (pick-best-color saturations colored)
    (lambda (v)
      (let ([my-move-colors ((available-move-colors saturations colored) v)])
        (if (set-member? root-vars v)
            (if (null? my-move-colors)
                (let ([sorted (sort (filter (lambda (e)
                                              (< e reg-num-start)
                                              (dict-ref saturations v))
                                            >))])
                  (foldl (lambda (n maximum)
                           (cond
                             [(< maximum n) maximum]
                             [(= maximum n) (- n 1)]
                             [(> maximum n) maximum]))
                         (- reg-num-start 1)
                         sorted))
                (max my-move-colors))
            (if (null? my-move-colors)
                (let ([sorted (sort (filter (compose not negative?) (dict-ref saturations v)) <)])
                  (foldl (lambda (n minimum)
                           (cond
                             [(< minimum n) minimum]
                             [(= minimum n) (+ n 1)]
                             [(> minimum n) minimum]))
                         0
                         sorted))
                (min my-move-colors))))))

  (define (assign-color! saturations)
    (lambda (colored v)
      (match v
        [(Reg r) (dict-set! colored v (hash-ref reg-num r))]
        [(Var name) (dict-set! colored v ((pick-best-color saturations colored) v))]
        [else (error "Unhandled locations:" v)])))

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
         [pque (make-pqueue
                (lambda (lhs rhs)
                  (match (cons lhs rhs)
                    [(cons (Reg _) _) #t]
                    [(cons _ (Reg _)) #f]
                    [else
                     (let ([lhs-satu-len (length (dict-ref saturations lhs))]
                           [rhs-satu-len (length (dict-ref saturations rhs))])
                       (cond
                         [(> lhs-satu-len rhs-satu-len) #t]
                         [(< lhs-satu-len rhs-satu-len) #f]
                         [(= lhs-satu-len rhs-satu-len)
                          (if (null? ((available-move-colors saturations colored) rhs)) #t #f)]))])))]
         [item-handles (make-hash)])

    (begin
      (for/list ([v vertices])
        (hash-set! item-handles v (pqueue-push! pque v)))
      (while (not (= (pqueue-count pque) 0))
             (let ([v (pqueue-pop! pque)])
               (when (not (mem-location? v))
                 ((assign-color! saturations) colored v)
                 (update-neighbors! v g saturations (dict-ref colored v))
                 (update-priority! pque item-handles v g))))
      ;; in case of empty interferecne graph
      (dict-set! colored (Reg 'rax) (hash-ref reg-num 'rax))
      colored)))

(define (num->mem n)
  (cond
    [(< n reg-num-start) (Deref 'r15 (* -8 (- reg-num-start n)))]
    [(< n reg-num-end) (Reg (dict-ref num-reg n))]
    [else (Deref 'rbp (* -8 (- n (- reg-num-end 1))))]))

(define (assign-arg colored)
  (lambda (arg)
    (match arg
      [(or (Reg _) (Var _)) (num->mem (dict-ref colored arg))]
      [(? mem-location?) arg]
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
      [(Instr 'movq (list s (Var x)))
       (if (hash-has-key? colored (Var x))
           (Instr 'movq (list ((assign-arg colored) s) ((assign-arg colored) (Var x))))
           (Instr 'nop '()))]
      [(Instr name args) (Instr name (map (assign-arg colored) args))]
      [else instr])))

(define (stack-size colored)
  (let ([num-on-stack (let ([num-color (apply max (dict-values colored))])
                        (if (>= num-color reg-num-end) (- num-color (- reg-num-end 1)) 0))])
    (* 8 num-on-stack)))

;; allocate-registers : pseudo-x86 -> pseudo-x86
(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (let ([colored (color-graph (dict-ref info 'conflict)
                                 (dict-ref info 'move-relation)
                                 (dict-ref info 'root-vars))])
       (X86Program
        (dict-set (dict-set (dict-set info 'stack-space (stack-size colored))
                            'used-callee
                            (filter (lambda (r) (set-member? callee-save r))
                                    (map (lambda (num) (hash-ref num-reg num))
                                         (filter (lambda (num)
                                                   (and (not (negative? num)) (< num reg-num-end)))
                                                 (dict-values colored)))))
                  'num-root-spills
                  (- reg-num-start (apply min (hash-values colored))))
        (dict-map/copy blocks
                       (lambda (label block)
                         (values label
                                 (Block '()
                                        (filter (lambda (instr)
                                                  (match instr
                                                    [(Instr 'nop _) #f]
                                                    [else #t]))
                                                (map (assign-homes-instr colored)
                                                     (Block-instr* block)))))))))]))

(define (block-has-only-prev? cfg label)
  (eq? (length (get-neighbors (transpose cfg) label)) 1))

(define ((merge-subsequent-block blocks cfg) label)
  (let* ([block (dict-ref blocks label)] [instrs (Block-instr* block)])
    (match (last instrs)
      [(Jmp next-label)
       (if (and (not (equal? next-label 'conclusion)) (block-has-only-prev? cfg next-label))
           (let* ([merged-instrs (append (take instrs (- (length instrs) 1))
                                         (Block-instr* (dict-ref blocks next-label)))]
                  [merged-block (Block '() merged-instrs)])
             (dict-remove (dict-set blocks label merged-block) next-label))
           blocks)]
      [else (error "unhandled cases" (last instrs))])))

;; remove-jumps : pseudo-x86 -> pseudo-x86
(define (remove-jumps p)
  (match p
    [(X86Program info blocks)
     (let ([cfg (dict-ref info 'control-flow-graph)] [labels (dict-keys blocks)])
       (X86Program info
                   (foldl (lambda (label merged-blocks)
                            (if (dict-has-key? merged-blocks label)
                                ((merge-subsequent-block merged-blocks cfg) label)
                                merged-blocks))
                          blocks
                          labels)))]))

(define (patch-instrs instrs)
  (apply
   append
   (map
    (lambda (instr)
      (match instr
        [(Instr name (list (Deref reg loc1) (Deref reg loc2)))
         (list (Instr 'movq (list (Deref reg loc1) (Reg 'rax)))
               (Instr name (list (Reg 'rax) (Deref reg loc2))))]
        [(Instr 'cmpq (list arg (Imm n)))
         (list (Instr 'movq (list (Imm n) (Reg 'rax))) (Instr 'cmpq (list arg (Reg 'rax))))]
        [(Instr 'movzbq (list byte-reg (Var x)))
         (list (Instr 'movzbq (list byte-reg (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Var x))))]
        [(Instr name (list (Imm n) arg))
         (if (> n 65536)
             (list (Instr 'movq (list (Imm n) (Reg 'rax))) (Instr name (list (Reg 'rax) arg)))
             (list instr))]
        [(Instr 'movq (list arg1 arg2)) (if (equal? arg1 arg2) '() (list instr))]
        [else (list instr)]))
    instrs)))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (X86Program info
                 (dict-map/copy blocks
                                (lambda (label block)
                                  (values label (Block '() (patch-instrs (Block-instr* block)))))))]))

(define (cp-label label)
  (match (system-type 'os)
    ['macosx (string->symbol (string-append "_" (symbol->string label)))]
    [else label]))

(define (aligned-rsp-offset info)
  (let* ([variables-space (dict-ref info 'stack-space)]
         [raw-stack-size (+ variables-space (* 8 (+ 2 (length (dict-ref info 'used-callee)))))])
    (if (= (modulo raw-stack-size 16) 8) (+ 8 variables-space) variables-space)))

(define (prelude info)
  (append (list (Instr 'pushq (list (Reg 'rbp)))
                (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                (Instr 'subq (list (Imm (aligned-rsp-offset info)) (Reg 'rsp))))
          (for/list ([reg (dict-ref info 'used-callee)])
            (Instr 'pushq (list (Reg reg))))
          ; initliaze rootstack and heap.
          (flatten (list (Instr 'movq (list (Imm (runtime-config:rootstack-size)) (Reg 'rdi)))
                         (Instr 'movq (list (Imm (runtime-config:heap-size)) (Reg 'rsi)))
                         (Callq 'initialize 2)
                         (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))
                         (for/list ([i (in-range 0 (dict-ref info 'num-root-spills))])
                           (list (Instr 'movq (list (Imm 0) (Deref 'r15 (* 8 i))))
                                 (Instr 'addq (list (Imm 8) (Reg 'r15)))))))
          (list (Jmp (cp-label 'start)))))

(define (conclusion info)
  (append (list (Instr 'subq (list (Imm (* 8 (dict-ref info 'num-root-spills))) (Reg 'r15))))
          (for/list ([reg (reverse (dict-ref info 'used-callee))])
            (Instr 'popq (list (Reg reg))))
          (list (Instr 'addq (list (Imm (aligned-rsp-offset info)) (Reg 'rsp)))
                (Instr 'popq (list (Reg 'rbp)))
                (Retq))))

;; TODO: no need to change %rsp if stack is empty
;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (X86Program info
                 (dict-set (dict-set blocks (cp-label 'main) (Block '() (prelude info)))
                           (cp-label 'conclusion)
                           (Block '() (conclusion info))))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ; ("partial evaluator" ,pe-Lfun ,interp-Lfun ,type-check-Lfun)
  `(("shrink" ,shrink ,interp-Lfun ,type-check-Lfun)
    ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
    ; ("expose allocation" ,expose-allocation ,interp-Lfun-prime ,type-check-Lfun)
    ; ("uncover get!" ,uncover-getbang ,interp-Lfun-prime ,type-check-Lfun)
    ; ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime ,type-check-Lfun)
    ; ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
    ; ("instruction selection" ,select-instructions ,interp-pseudo-x86-2)
    ; ("uncover live" ,uncover-live ,interp-pseudo-x86-2)
    ; ("build interference" ,build-interference ,interp-pseudo-x86-2)
    ; ("allocate registers" ,allocate-registers ,interp-pseudo-x86-2)
    ; ("remove jumps" ,remove-jumps ,interp-pseudo-x86-2)
    ; ("patch instructions" ,patch-instructions ,interp-x86-2)
    ; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-2)
    ; ))
    ))
