#lang racket
(require racket/set racket/stream)
(require graph/graph/graph/main)
(require "utilities.rkt")
(require "priority_queue.rkt")

(provide uncover-live-pass)
(provide uncover-live-pass-test)
(provide build-interference-pass)
(provide get-key-info)

(define (Imm? e)
  (match e
    [(Imm n) #t]
    [else #f]
   ))


(define (loc-write instr)
  (match instr
    [(Instr 'addq (list lhs rhs)) (set rhs)]
    [(Instr 'subq (list lhs rhs)) (set lhs)]
    [(Instr 'negq (list lhs))     (set lhs)]
    [(Instr 'movq (list lhs rhs)) (set rhs)]
    [(Callq name arity)           (caller-save-for-alloc)]
    [(Jmp target)                 (set)]
   )) 

(define (loc-read instr)
  (match instr
    [(Instr 'addq (list (? Imm? lhs) rhs)) (set rhs)]
    [(Instr 'addq (list lhs rhs)) (set lhs rhs)]
    [(Instr 'subq (list lhs (? Imm? rhs))) (set lhs)]
    [(Instr 'subq (list lhs rhs)) (set lhs rhs)]
    [(Instr 'negq (list lhs))     (set lhs)]
    [(Instr 'movq (list (? Imm? lhs) rhs)) (set)]
    [(Instr 'movq (list lhs rhs)) (set lhs)]
    [(Callq name arity)           (callee-save-for-alloc)]
    [(Jmp target)                 (set)];(set (Reg 'rax) (Reg 'rsp))]
   ))

;acum = list of all set 
(define (calc-post-set instr accum)
  (let ([curr-set
          (set-union (set-subtract (car accum) (loc-write instr)) (loc-read instr))])
       (cons curr-set accum
       )))

;output - list of liveness set 
(define (live-post-set instrs begin-set)
  (cdr (foldr
          calc-post-set
          (list begin-set)
          instrs)))

(define (uncover-live-pass p)
  (match p
   [(X86Program info body)
     (X86Program
      (dict-set info 'live-set (live-post-set (Block-instr* (dict-ref body 'start)) (set)))
      body)]))
                #|  (list
                      (cons 'start
                           (Block '() (Block-instr* (dict-ref body 'start))))
                      (cons 'main
                           (Block '() (create-main info)))
                      (cons 'conclusion
                           (Block '() (create-conclusion info)))
                  ))])) |#

(define (uncover-live-pass-test p)
  (match p
   [(X86Program info body)
     (live-post-set (Block-instr* (dict-ref body 'start)) (set))]))

;------------------------------------------------------------------
;------------------------------------------------------------------
;1. If instruction I_k is a move such as movq s, d, then add the edge (d, v) for every v ∈ L_after(k) unless v = d or v = s.
;2. For any other instruction I_k, for every d ∈ W(k) add an edge (d, v)
;for every v ∈ L_after(k) unless v = d.

;output - list of pair overlap verticess
(define (check-interference live-set instr)
  (match instr
    [(Instr 'movq (list lhs rhs))
            (for/list ([live (set->list live-set)]
                #:when (and (not (equal? live lhs)) (not (equal? live rhs))))
              (cons rhs live))]
    [else 
          (for*/list 
             ([w-loc    (loc-write instr)]
              [live-loc live-set]
              #:when (not (equal? live-loc w-loc)))
           (cons live-loc w-loc))]
 ))

(define (build-interference-pass p)
  (match p
   [(X86Program info body)
     (let ([graph (map check-interference 
                       (dict-ref info 'live-set) 
                       (Block-instr* (dict-ref body 'start)))])
     (X86Program  
       (dict-set info 'conflicts (undirected-graph (list 0 1)));(if (equal? graph '()) (undirected-graph (list 0 1)) (undirected-graph graph)))
       body))]
))

(define (get-key-info p key)
  (match p
   [(X86Program info body) (dict-ref info key)]))
;;-----------------------------------------------------------------------------------------------------------------------------
(define (reg? p)
  (match p
   ; [(Reg name) #t]
    ['b #t]
    [else #f]))

(define (var? p)
  (match p
    [(Var x) #t]
    [else #f]))

(define (partial f graph)
  (lambda var
    (apply f graph var)))

(define (reg->int reg)
  -1)

(define (create-satur-base graph var)
  (list var -1 (map
                reg->int
                (filter reg?
                       (sequence->list (in-neighbors graph var))))))

;input: element = (name, int, list of int)
;output:
(define (find-max e accum)
  (cond
    [(not (equal? -1 (second e))) accum]
    [(empty? accum) e]
    [(> (length (third accum)) (length(third e))) accum]
    [else e]))

;input element, max element, list of neighbors of max element
(define (dsatur-pass elt max-elt neighbors-of-max)
  (cond
    [(equal? (car elt) (car max-elt))
     max-elt]
    ;return elt with update list neighbors - include max name
    [(member (car elt) neighbors-of-max)
     (list
      (car elt)
      (cadr elt)
      (append (caddr elt) (car max-elt)))]
    [else elt]))

(define (partial2 f max-elt neighbors-of-max)
  (lambda (var)
    (f var max-elt neighbors-of-max)))

;output - list of (var, order(color №))
(define (color-graph graph var-list)
  (let* ([satur-list (map (partial create-satur-base graph) var-list)]
         [max-satur (foldl find-max '() satur-list)])
    (print satur-list)
    (map (partial2 dsatur-pass
                   max-satur
                  (sequence->list (in-neighbors graph (car max-satur))))
        satur-list)   
   ))
; find max
; find empty index
; set index into max and set this index into neighbors
; repeat

;(define g (undirected-graph '((a b) (b c) (c d))))
;(get-edges g)
;(color-graph g '(a b c d))