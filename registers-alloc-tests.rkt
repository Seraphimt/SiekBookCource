#lang racket
(require "utilities.rkt")
(require "registers-alloc.rkt")


;----liveness------------------------------------------------------------------
;----tests---------------------------------------------------------------------
(define test-liveness-0 
(list
  (Instr' movq (list (Imm 42) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-liveness-0 
(list
  (set) ;from jmp
  (set) ;from start base
))
;------------------------------------------------------------------------------
(define test-liveness-1 
(list     
  (Instr 'movq (list (Imm 24) (Var 'a)))
  (Instr 'movq (list (Imm 18) (Var 'b)))
  (Instr 'addq (list (Var 'a) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-liveness-1 
(list
  (set (Var 'a))
  (set (Var 'a) (Var 'b))
  (set (Var 'b))
  (set) ;from jmp
  (set) ;from start base
))
;-------------------------------------------------------------------------
(define test-liveness-2 
(list     
  (Instr 'movq (list (Imm 52) (Var 'a)))
  (Instr 'movq (list (Imm 10) (Var 'b)))
  (Instr 'subq (list (Var 'a) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-liveness-2 
(list
  (set (Var 'a))
  (set (Var 'a) (Var 'b))
  (set (Var 'b))
  (set) ;from jmp
  (set) ;from start base
))
;-------------------------------------------------------------------------
(define test-liveness-3 
(list     
  (Instr 'movq (list (Imm 99) (Var 'a)))
  (Instr 'movq (list (Imm 10) (Var 'b)))
  (Instr 'addq (list (Imm 32) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-liveness-3 
(list
  (set)
  (set (Var 'b))
  (set (Var 'b))
  (set) ;from jmp
  (set) ;from start base
))
;-------------------------------------------------------------------------
(define test-liveness-4 
(list     
  (Instr 'movq (list (Imm 42) (Var 'a)))
  (Instr 'movq (list (Imm 10) (Var 'b)))
  (Instr 'movq (list (Var 'a) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-liveness-4 
(list
  (set)
  (set (Var 'b))
  (set (Var 'b))
  (set) ;from jmp
  (set) ;from start base
))
;-------------------------------------------------------------------------
(define (create-test-case instrs)
  (X86Program 
  '() 
  (list (cons 
    'start 
    (Block '() instrs
      )))))

(define test-suit-liveness
  (list 
    (create-test-case test-liveness-0)
    (create-test-case test-liveness-1)
    (create-test-case test-liveness-2)
    (create-test-case test-liveness-3)
  ))
  
(define etalon-suit-liveness
  (list 
    etalon-liveness-0
    etalon-liveness-1
    etalon-liveness-2
    etalon-liveness-3
  ))

(define test-No ;temp
  (list 
    0
    1
    2
    3
  ))
;-------------------------------------------------------------------------
(define (check-live test-suit etalon-suit)
(map 
  (lambda (test etalon No)
    (let ([test (uncover-live-pass-test test)])
       (println No)
       (if (andmap equal? etalon test) (println "passed") (begin (println "fail") (print "etalon:") (println etalon) (print "test  :") (println test)))))
  test-suit
  etalon-suit
  test-No
))


(check-live test-suit-liveness etalon-suit-liveness)
