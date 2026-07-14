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
(define test-liveness-5 
(list     
  (Instr 'movq (list (Imm 42) (Var 'a)))
  (Instr 'movq (list (Imm 10) (Var 'b)))
  (Instr 'movq (list (Var 'a) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-liveness-5 
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
    (create-test-case test-liveness-4)
    (create-test-case test-liveness-5)
  ))
  
(define etalon-suit-liveness
  (list 
    etalon-liveness-0
    etalon-liveness-1
    etalon-liveness-2
    etalon-liveness-3
    etalon-liveness-4
    etalon-liveness-5
  ))

(define test-No ;temp
  (list 
    0
    1
    2
    3
    4
    5
  ))
;-------------------------------------------------------------------------
(define (check-live test-suit etalon-suit)
(map 
  (lambda (test etalon No)
    (let ([test (uncover-live-pass-test test)])
       (println No)
       (if (andmap equal? etalon test) 
           (println "passed") 
           (begin (println "fail") (print "etalon:") (println etalon) (print "test  :") (println test)))))
  test-suit
  etalon-suit
  test-No
))


(check-live test-suit-liveness etalon-suit-liveness)

;----overlap-graph-build-------------------------------------------------------
;----tests---------------------------------------------------------------------



(define etalon-build-graph-0 
(undirected-graph '()))

;-------------------------------------------------------------------------
(define test-suit-build-graph
  (list 
    (create-test-case test-liveness-0)
  ))
  
(define etalon-suit-build-graph
  (list 
    etalon-build-graph-0
  ))
;-------------------------------------------------------------------------
(define (check-graph test-suit etalon-suit)
(map 
  (lambda (test etalon No)
    (let ([test (get-conflicts(build-interference-pass(uncover-live-pass test)))])
       (println No)
       (if (andmap equal? etalon test) 
           (println "passed") 
           (begin (println "fail") (print "etalon:") (println etalon) (print "test  :") (println test)))))
  test-suit
  etalon-suit
  test-No
))

(check-graph test-suit-build-graph etalon-suit-build-graph)
;-------------------------------------------------------------------------

(define (pass-check test-suit etalon-suit)
(map 
  (lambda (test etalon No)
    (let ([test (get-conflicts(build-interference-pass(uncover-live-pass test)))])
       (println No)
       (if (andmap equal? etalon test) 
           (begin (println "passed") #t)
           (begin (println "fail") (print "etalon:") (println etalon) (print "test  :") (println test) #f))))
  test-suit
  etalon-suit
  test-No
))

(define (pass-check program test etalon)
(map 
  (lambda (test etalon No)
    (let ([test (get-conflicts(build-interference-pass(uncover-live-pass test)))])
       (println No)
       (if (andmap equal? etalon test) 
           (begin (println "passed") #t)
           (begin (println "fail") (print "etalon:") (println etalon) (print "test  :") (println test) #f))))
  etalon
  test-No
))

(define passes 
(list uncover-live-pass))

(define tests 
'())

(define (check-one data passes checkers)
(
let ([transform-data ((car passes) data)])
  (if ((car checkers) transform-data)
      (check-one transform-data (cdr passes) (cdr checkers))
      #void)
))

(define (check datas passes checkers)
(
  for ([data datas]) (check-one data passes checkers))
)

(check test-suit-liveness passes checkers)
;data -> pass1 -> check1 -> (if correct) -> pass2 -> check2 -> ...
