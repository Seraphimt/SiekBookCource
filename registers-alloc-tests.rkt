#lang racket
(require graph/graph/graph/main)
(require "utilities.rkt")
(require "registers-alloc.rkt")


;----liveness------------------------------------------------------------------
;----tests---------------------------------------------------------------------
(define test-alloc-0 
(list
  (Instr' movq (list (Imm 42) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-alloc-0 
(list  
  (list
    (set) ;from jmp
    (set) ;from start base
   )
 (undirected-graph (list 0 1))
 ;'()
))
;------------------------------------------------------------------------------
(define test-alloc-1 
(list     
  (Instr 'movq (list (Imm 24) (Var 'a)))
  (Instr 'movq (list (Imm 18) (Var 'b)))
  (Instr 'addq (list (Var 'a) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-alloc-1 
(list
  (list
    (set (Var 'a))
    (set (Var 'a) (Var 'b))
    (set (Var 'b))
    (set) ;from jmp
    (set) ;from start base
  ) 
  (undirected-graph (list (cons (Var 'b) (Var 'a))))
 ; (list
   ; (cons 'a 0)
  ;  (cons 'b 1)
 ; )
))
;-------------------------------------------------------------------------
(define test-alloc-2 
(list     
  (Instr 'movq (list (Imm 52) (Var 'a)))
  (Instr 'movq (list (Imm 10) (Var 'b)))
  (Instr 'subq (list (Var 'a) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-alloc-2
(list
  (list
    (set (Var 'a))
    (set (Var 'a) (Var 'b))
    (set (Var 'b))
    (set) ;from jmp
    (set) ;from start base
  )
  (undirected-graph (list (cons (Var 'b) (Var 'a))))
))
;-------------------------------------------------------------------------
(define test-alloc-3 
(list     
  (Instr 'movq (list (Imm 99) (Var 'a)))
  (Instr 'movq (list (Imm 10) (Var 'b)))
  (Instr 'addq (list (Imm 32) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-alloc-3 
(list
  (list
    (set)
    (set (Var 'b))
    (set (Var 'b))
    (set) ;from jmp
    (set) ;from start base
  )
  (undirected-graph '(0 1)) 
))
;-------------------------------------------------------------------------
(define test-alloc-4 
(list     
  (Instr 'movq (list (Imm 42) (Var 'a)))
  (Instr 'movq (list (Imm 10) (Var 'b)))
  (Instr 'movq (list (Var 'a) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-alloc-4 
(list
  (list
    (set (Var 'a))
    (set (Var 'a))
    (set (Var 'b))
    (set) ;from jmp
    (set) ;from start base
  )
  (undirected-graph '(0 1)) 
))
;-------------------------------------------------------------------------
(define test-alloc-5 
(list     
  (Instr 'movq (list (Imm 32)   (Var 'a)))
  (Instr 'movq (list (Imm 10)   (Var 'b)))
  (Instr 'movq (list (Var 'a)   (Reg 'rax)))
  (Instr 'movq (list (Reg 'rax) (Var 't) ))
  (Instr 'movq (list (Var 'b)   (Reg 'rax)))
  (Instr 'addq (list (Reg 'rax) (Var 't)))
  (Instr 'movq (list (Var 't)   (Reg 'rax)))
  (Jmp 'conclusion)))
  
(define etalon-alloc-5
(list
  (list
    (set (Var 'a))
    (set (Var 'a) (Var 'b))
    (set (Var 'b))
    (set (Var 't))
    (set (Var 't))
    (set) ;from jmp
    (set) ;from start base
  )
  (undirected-graph (list (cons (Var 'a) (Var 'b)))) 
))
;-------------------------------------------------------------------------
(define test-alloc-6 
(list     
  (Instr 'movq (list (Imm 20) (Var 'b)))
  (Instr 'movq (list (Imm 1)  (Var 'a)))
  (Instr 'addq (list (Var 'b) (Var 'a)))
  (Instr 'movq (list (Imm 21) (Var 'c)))
  (Instr 'movq (list (Var 'a) (Var 't)))
  (Instr 'addq (list (Var 'c) (Var 't)))
  (Instr 'movq (list (Var 't) (Reg 'rax)))
  (Jmp 'conclusion)))
  
(define etalon-alloc-6
(list
  (list
    (set (Var 'b))
    (set (Var 'a) (Var 'b))
    (set (Var 'a))
    (set (Var 'a) (Var 'c))
    (set (Var 'c) (Var 't))
    (set (Var 't))
    (set) ;from jmp
    (set) ;from start base
   )
 (undirected-graph 
   (list 
     (cons (Var 'a) (Var 'b))
     (cons (Var 'a) (Var 'c))
     (cons (Var 'c) (Var 't))
    )) 
))
;-------------------------------------------------------------------------
(define (create-test-case instrs)
  (X86Program 
  '() 
  (list (cons 
    'start 
    (Block '() instrs
      )))))
  
(define test-suit-alloc
  (list 
    (create-test-case test-alloc-0)
    (create-test-case test-alloc-1)
    (create-test-case test-alloc-2)
    (create-test-case test-alloc-3)
    (create-test-case test-alloc-4)
    (create-test-case test-alloc-5)
    (create-test-case test-alloc-6)
  ))
  
(define etallon-alloc 
  (list 
    etalon-alloc-0
    etalon-alloc-1
    etalon-alloc-2
    etalon-alloc-3
    etalon-alloc-4
    etalon-alloc-5
    etalon-alloc-6
))
;; add negative test ?
(define (common-checker test etalon name shower)
(begin
  (display name)
  (display ":")
  (if (equal? etalon test) 
      (begin (displayln " passed") #t)
      (begin (displayln " fail") (display "etalon:") (println (shower etalon)) (display "test  :") (println  (shower test)) #f))
))

(define (liveness-checker program etalon)
(
  common-checker (get-key-info program 'live-set) etalon "build liveness" identity
))

(define (graph-conflicts-checker program etalon)
(
  common-checker (get-key-info program 'conflicts) etalon "build conflicts" get-vertices
))

(define passes-alloc 
  (list 
  uncover-live-pass
  build-interference-pass
))

(define checkers-alloc 
  (list 
  liveness-checker
  graph-conflicts-checker
))

(define (check-one test passes checkers etalons)
(
if (empty? passes)
(values)   
(let ([transform-test ((car passes) test)])
  (if ((car checkers) transform-test (car etalons)) 
      (check-one transform-test (cdr passes) (cdr checkers) (cdr etalons))
      (values)) ; (void)
)))

(define (check tests passes checkers etalons)
(
  for ([test tests]
       [etalon-for-id etalons]
       [id (in-range (length tests))])
     (displayln id)
     (check-one test passes checkers etalon-for-id) 
))

(check test-suit-alloc passes-alloc checkers-alloc etallon-alloc)


