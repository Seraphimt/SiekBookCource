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
    [(Prim '+ (list (Int n) rhs)) ((Prim '+ (list (Int (fx- 0 n)) rhs)))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2))   (Int (fx+ n1 n2))]
    [((Int n1) (Prim '+ (list (Int n2) rhs)))   (Prim '+ (list (Int (fx+ n1 n2)) rhs))]
    [((Int n1) _)   (Prim '+ (list (Int n1) r2))]

    [((Prim '+ (list (Int n1) rhs))(Int n2))  (Prim '+ (list (Int (fx+ n1 n2)) rhs))]
    [((Prim '+ (list (Int n1) rhs1))    (Prim '+ (list (Int n2) rhs2))) (Prim '+ (list (Int (fx+ n1 n2)) (Prim '+ (list rhs1 rhs2))))] 
    [((Prim '+ (list (Int n1) rhs1)) _) (Prim '+ (list (Int n1)) (Prim '+ (list rhs1 r2)))]

    [(_ (Int n1))  (Prim '+ (list (Int n1) r1))]
    [(_ (Prim '+ (list (Int n1) rhs)))  (Prim '+ (list (Int n1) (Prim '+ (list r1 rhs))))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1) (pe-neg (pe-exp e2)))]
    [(Let x expr body) (Let x (pe-exp expr) (pe-exp body))]
    ))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let ([new-env (dict-set env x (gensym x))]) 
          (Let (dict-ref new-env x)
               ((uniquify-exp env) e)
               ((uniquify-exp new-env) body)
           ))
      ]
      [(Prim op arg)
       (Prim op (for/list ([e arg]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-operand : Lvar -> Lvar^mon

(define (atom? expr)
  (match expr
    [(Var x) #t]
    [(Int n) #t]
    [else #f]
   )
)

(define (expr? expr)
  (not (atom? expr)))

(define (rco-atom e)
    (match e
      [(Prim op args)  (cons  (gensym "tmp") (rco-expr e)) ]
      [(Let x y z) (cons  (gensym "tmp") (rco-expr e)) ]
      [else (rco-expr e)]
      ))

(define (rco-expr e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Prim 'read args) (let ([name (gensym "tmp")]) (Let name e (Var name)))]
      
      [(Prim op (list (? atom? atom) (? expr? expr)) )
       (let ([res-atom  (rco-atom expr)])
         (Let (car res-atom) (cdr res-atom)  
          (Prim op (list atom (Var (car res-atom))))))
      ]
      
     [(Prim op (list (? expr? expr) (? atom? atom)) )
       (let ([res-atom  (rco-atom expr)])
         (Let (car res-atom) (cdr res-atom)  
          (Prim op (list (Var (car res-atom)) atom))))
      ]
     [(Prim op (list (? expr? expr1) (? expr? expr2)) )
       (let ([res-atom1  (rco-atom expr1)])
         (let ([res-atom2  (rco-atom expr2)])
           (Let (car res-atom1) (cdr res-atom1)
                (Let (car res-atom2) (cdr res-atom2) 
                    (Prim op (list (Var (car res-atom1)) (Var (car res-atom2))))))))
      ]
      [(Let x rhs body) (Let x (rco-expr rhs) (rco-expr body))]
      [(Program '() ex) (rco-expr ex)]
      [else e]
 ))

(define (remove-complex-operand p)
  (match p
    [(Program info e) (Program info (rco-expr p))]))


(define (check-rco-mine p)
  (match p
    [(Var x) '()]
    [(Int n) '()]
    [(Prim op args) (for/list ([e args]) (if (expr? e) (error "Non Atomic: " e) '()))]
    [(Let x rhs body) (list (check-rco-mine rhs) (check-rco-mine body))]
    [(Program info e) (check-rco-mine e)]
    ))

;(check-rco-mine (remove-complex-operand(parse-program '(program () (let ([y1 10]) (+ y1 (let ([y2 10]) (+ y2 5)))) ))))


;(rco-expr (parse-program '(program () (read))))
;(rco-expr (parse-program '(program () (+ 10 (- 10 (+ 10 32))))))
;(rco-expr (parse-program '(program () (+ (- 10) (- 12)))))
;(rco-expr (parse-program '(program () 42)))

;(rco-expr (parse-program '(program ()(+(let [(x (+ 100 (- 10)))] (+ (- 10) (+ 12 (- 100 x)))) (- 111)))))
;(rco-expr (parse-program '(program ()(+ (let [(x (+ 100 (- 12)))] (+ x 10)) (- 111)))))
;(rco-expr (parse-program '(program ()(+ (- 11331) (- 111)))))
;(remove-complex-operand (parse-program '(program ()(let ([a 42])(let ([b 10])  (+ a b))))))
;(remove-complex-operand (parse-program '(program ()(let ([a 42])(let ([b a])  b)))))
;(remove-complex-operand (parse-program '(program ()(let ([y1 10]) (+ y1 (let ([y2 12]) (+ y2 5)))))))
;(remove-complex-operand (parse-program '(program ()(+ (- 16) (let ([y2 10]) (+ y2 5))))))
; more tests with Let

;; explicate-control : Lvar^mon -> Cvar

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate-assign x rhs (explicate-tail body))]
    [(Prim op args) (let ([x (Var (gensym "tmp"))]) (Seq (Assign x (Prim op args)) (Return x)))]
    
    [else (error "explicate-tail unhndled case" e)]
    ))

(define (explicate-assign x rhs cont)
  (match rhs
    [(Var x1) (Seq (Assign (Var x) (Var x1)) cont)]
    [(Int n)  (Seq (Assign (Var x) (Int n)) cont)]
    [(Let x1 rhs1 body) (explicate-assign x1 rhs1 (explicate-assign x body cont)) ] ;(Seq (Assign (Var x1) (explicate-assign x rhs1 cont) cont))]
    [(Prim op args) (Seq (Assign (Var x) (Prim op args)) cont)]
    
    [else (error "explicate-assign unhndled case" rhs)]
    ))
;(Seq (Assign (Var 'y3) (Int 12)) (Return (Prim '+ (list (Var 'y2) (Var 'y1)))))
;(Seq (Assign (Var 'y1) (Int 10)) (Seq (Assign (Var 'y3) (Int 12)) (Return (Prim '+ (list (Var 'y2) (Var 'y1))))))
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (dict-set '() 'start (explicate-tail body)))]))
 
;(explicate-control (parse-program '(program () 42)))
;(explicate-control (parse-program '(program () (+ (- 10) (- 12)))))
;(explicate-control (parse-program '(program ()(let ([y1 10]) (+ y1 (let ([y2 10]) (+ y2 5)))))))
;(explicate-control (parse-program '(program () (let ([y1 10]) (+ y1 (let ([y2 12]) (+ y2 5)))))))
;(explicate-control (parse-program '(program () (let ([y1 10]) (let ([y2 (let ([y3 12])  (+ y3 5))]) (+ y2 y1))))))
;(explicate-control (parse-program '(program () (let ([a (let ([b 10]) (+ b 1))]) (let ([c 10]) (+ a c))))))
;(explicate-control (parse-program '(program ()(let ([a (let ([b (let ([d 10]) (let ([f 12]) (+ d f))) ]) (+ b 1))]) (let ([c 10])(+ a c))))))


;; select-instructions : Cvar -> x86var
(define (select-atom expr)
  (match expr
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    
    [else (error "select-atom unhndled case" expr)]
   ))

(define (create-add-instr var l r)
(let* ([atom-l (select-atom l)]
       [atom-r (select-atom r)])
  (cond
    [(equal? var atom-l) (list (Instr 'addq (list atom-r var)))]
    [(equal? var atom-r) (list (Instr 'addq (list atom-l var)))]    
    [else (list (Instr 'movq (list atom-l var)) (Instr 'addq (list atom-r var)))]
   )))

(define (select-stm e)
  (match e
    [(Assign var (Prim '+ (list l r)))   (create-add-instr var l r)]
    [(Assign var (Prim '- (list l r)))   (list (Instr 'movq (list (select-atom l) var)) (Instr 'subq (list (select-atom r) var)))]
    [(Assign var (Prim '- (list unary))) (list (Instr 'movq (list (select-atom unary) var)) (Instr 'negq (list var)))]     

    [(Assign var (Prim 'read '())) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) var)))]
    
    [(Assign var (Var x)) (list (Instr 'movq (list x var)))]
    [(Assign var (Int n)) (list (Instr 'movq (list (Imm n) var)))]
    
    
    [else (error "select-stm unhandled case" e)]
   ))

(define (select-tail p)
  (match p
    [(Seq stm tail) (append (select-stm stm) (select-tail tail))]
    [(Return expr)  (list (Instr 'movq (list (select-atom expr) (Reg 'rax))) (Jmp 'conclusion))] ; goto epilog ?  (Instr 'jmp (list 'conclusion))
    )
)

(define (select-instructions p)
 (match p
    [(CProgram info body) (X86Program info (list (cons 'start (Block '() (select-tail (dict-ref body 'start))))))]))

;(explicate-control (parse-program '(program () (+ 12 42))))
;(select-instructions(explicate-control (parse-program '(program () 42))))
;(select-instructions(explicate-control (parse-program '(program () (+ 12 42)))))
;(select-instructions(explicate-control (parse-program '(program () (- 11331)))))
;(select-instructions(explicate-control (parse-program '(program () (read)))))


;; assign-homes : x86var -> x86var
(define (calc-stack-size n)
   (if (equal? (remainder n 16) 0)
       n
       (* (+ (quotient n 16) 1) 16)
))

(define (type-size type)
  (match type
    [Integer 8]
    [else (error "wrong type" type)]  
   )
 )
;;alist =  ((x Integer) (y Integer) ...)
;;result = ((x -8) (y -16) ...) ; . stack_size
(define (add-var-to-storage alist n)
  (if (empty? alist)
      (list* (cons 'stack-size (calc-stack-size (- (+ n 8)))) '())
      (let* ([var  (car (car alist))]
             [type (cdr (car alist))])
        (list* (cons var n) (add-var-to-storage (cdr alist) (- n (type-size type))))
      ))
)

(define local (list (cons 'x 'Integer) (cons 'y 'Integer) (cons 'z 'Integer)))
(add-var-to-storage local -8)
;Output: '((x . -8) (y . -16) (z . -24))

(define (create-local info)
  (add-var-to-storage (dict-ref info 'locals-types) -8))

(define (assign-homes-impl e info var-storage)
  (match e
  [(Instr name args) (Instr name (for/list ([arg args]) (assign-homes-impl arg info var-storage)))]

  [(Var x) (Deref 'rbp (dict-ref var-storage x))]
                  
  [(Imm n) (Imm n)]
  [(Reg r) (Reg r)]
  [(Jmp j) (Jmp j)]
  [(Callq name arity) (Callq name arity)]   
  [else (error "assign-homes unhandled case" e)]
  )
)

(define (assign-homes p)
   (match p
    [(X86Program info body)
     (let ([local-list (create-local info)]) 
       (X86Program (dict-set info 'stack-space (dict-ref local-list 'stack-size))
                   (list
                        (cons 'start
                              (Block '()
                                     (for/list ([instract (Block-instr* (dict-ref body 'start))])
                                      (assign-homes-impl instract info local-list) ))))))]
 ))

;; patch-instructions : x86var -> x86int
(define (add-instr instrs-list)
  (if (empty? instrs-list)
      '()      
      (let ([instr (car instrs-list)])
         (match instr
          [(Instr name (list (Deref name1 offset1) (Deref name2 offset2)))
           (list*
             (Instr 'movq (list (Deref name1 offset1) (Reg 'rax)))
             (Instr name (list (Reg 'rax) (Deref name2 offset2)))
             (add-instr (cdr instrs-list)))]
          [else (list* instr (add-instr (cdr instrs-list)))]
))))

(define (patch-instructions p)
   (match p
    [(X86Program info body)
     (X86Program info (list
                       (cons 'start
                             (Block '()
                                    (add-instr (Block-instr* (dict-ref body 'start)))))))]   
 ))

;; prelude-and-conclusion : x86int -> x86int
(define (create-main info)
  (list
     (Instr 'pushq (list (Reg 'rbp)))
     (Instr 'movq  (list (Reg 'rsp) (Reg 'rbp)))
     (Instr 'subq  (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
     (Jmp 'start)
   )
 )

(define (create-conclusion info)
  (list
     (Instr 'addq  (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
     (Instr 'popq  (list (Reg 'rbp)))
     (Retq)
   )
 )

(define (create-start instrs) instrs
  (append 
     instrs
     (list (Jmp 'conclusion))))

(define (prelude-and-conclusion p)
(match p
    [(X86Program info body)
     (X86Program info
                 (list
                   (cons 'start
                        (Block '() (Block-instr* (dict-ref body 'start))))
                   (cons 'main
                        (Block '() (create-main info)))
                   (cons 'conclusion
                        (Block '() (create-conclusion info)))
                  ))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
      ("particaly eval", pe-Lint, interp_Lvar, type-check-Lvar)
      ("uniquify" ,uniquify ,interp_Lvar ,type-check-Lvar)
      ("remove complex operand" ,remove-complex-operand ,interp_Lvar ,type-check-Lvar)
      ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
      ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
      ("assign homes" ,assign-homes ,interp-x86-0)
      ("patch instructions" ,patch-instructions ,interp-x86-0)
      ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

;(print-x86

(debug-level 1)
(AST-output-syntax 'concrete-syntax)

(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

;; The following tests the intermediate-language outputs of the passes.
(interp-tests "var_test" #f compiler-passes interp_Lvar "var_test" (tests-for "var"))