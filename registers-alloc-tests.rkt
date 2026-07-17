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
  (undirected-graph
  '()
  )
)
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
  (undirected-graph
  '()
  )
)
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
  (undirected-graph
  '()
  )
)
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
  (undirected-graph
  '()
  )
)
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
    (set)
    (set (Var 'b))
    (set (Var 'b))
    (set) ;from jmp
    (set) ;from start base
  )
  (undirected-graph
  '()
  )
)
;-------------------------------------------------------------------------
(define test-alloc-5 
(list     
  (Instr 'movq (list (Imm 42) (Var 'a)))
  (Instr 'movq (list (Imm 10) (Var 'b)))
  (Instr 'movq (list (Var 'a) (Var 'b)))
  (Instr 'movq (list (Var 'b) (Reg 'rax)))
  (Jmp 'conclusion)))

(define etalon-alloc-5
(list
  (list
    (set)
    (set (Var 'b))
    (set (Var 'b))
    (set) ;from jmp
    (set) ;from start base
   )
   (undirected-graph
     '()
   )
)
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


;(check-live test-suit-liveness etalon-suit-liveness)

;----overlap-graph-build-------------------------------------------------------
;----tests---------------------------------------------------------------------

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

;-------------------------------------------------------------------------

(define test-suit-alloc
  (list 
    (create-test-case test-liveness-0)
    (create-test-case test-liveness-1)
    (create-test-case test-liveness-2)
    (create-test-case test-liveness-3)
    (create-test-case test-liveness-4)
    (create-test-case test-liveness-5)
  ))

(define (common-checker test etalon comparator id)
(begin     
  (println id)
  (if (comparator etalon test) 
      (begin (println "passed") #t)
      (begin (println "fail") (print "etalon:") (println etalon) (print "test  :") (println test) #f))
))

(define (liveness-checker program etalon id)
(
  common-checker (get-key-info program 'live-set) etalon equal? id
))

(define (graph-conflicts-checker program etalon id)
(
  common-checker (get-key-info program 'conflicts) etalon equal? id
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

(define etallon-alloc 
  (list 
    etalon-alloc-0
    etalon-alloc-1
    etalon-alloc-2
    etalon-alloc-3
    etalon-alloc-4
    etalon-alloc-5
))

(define (check-one test passes checkers etalons id)
(
let ([transform-test ((car passes) test)]) ;apply
  (if ((car checkers) transform-test (car etalons) id) 
      (check-one transform-test (cdr passes) (cdr checkers) (cdr etalons))
      (values)) ; (void)
))

(define (check tests passes checkers)
(
  for* ([test tests]
        [id (in-range 5)]) 
       (check-one test passes checkers id))
)

(check test-suit-alloc passes-alloc checkers-alloc)


;data -> pass1 -> check1 -> (if correct) -> pass2 -> check2 -> ...
; (list test etalon No)
;test (list etalons)
; 
;negative test
