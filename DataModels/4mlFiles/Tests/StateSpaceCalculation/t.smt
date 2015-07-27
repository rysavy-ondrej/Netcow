(declare-datatypes () ((Flow (mk-flow (srcip (_ BitVec 32)) (srcpn (_ BitVec 16)) (dstip (_ BitVec 32)) (dstpn (_ BitVec 16)) (proto (_ BitVec 16))))))

; unsat ~ Flow \subseteq Filter:
(define-fun Includes ((filter Bool)(flow Bool)) Bool (and flow (not filter)))

; unsat ~ Flow \cap Filter = \empty
(define-fun Disjoint ((filter Bool)(flow Bool)) Bool (and flow filter))


(define-fun null-flow ((x Flow)) Bool (= x (mk-flow #x00000000 #x0000 #x00000000 #x0000 #x0000 ) ))

(define-fun T_1 ((x Flow)(y Flow)) Bool
  (ite (and (bvuge (dstip x) #x20000000) (bvule (dstip x) #x20ffffff)) (= y x) (null-flow y))
)

(define-fun T_2 ((x Flow)(y Flow)) Bool
  (ite (and (bvuge (dstip x) #x20000000) (bvule (dstip x) #x20ffffff)
            (bvuge (srcip x) #x10000000) (bvule (srcip x) #x10ffffff)
       ) (= y x) (null-flow y))
)

(define-fun T_3 ((x Flow)(y Flow)) Bool
  (ite (and (bvuge (dstip x) #x30000000) (bvule (dstip x) #x30ffffff)) (= y x) (null-flow y))
)
									
(define-fun T_4 ((x Flow)(y Flow)) Bool (T_3 x y))

; This is path transformation:
(define-fun R ((x Flow)(y Flow)) Bool (exists ((x1 Flow)(x2 Flow)(x3 Flow)) (and (= x x1) (T_1 x1 x2) (T_2 x2 x3) (= x3 y)) ) )

; This is a precondition:
(define-fun P ((x Flow)) Bool (and (= (srcip x) #x10111111) (= (dstip x) #x20222222) ) )

; This is a postcondition
(define-fun Q ((y Flow)) Bool (and (= (srcip y) #x10111111) (= (dstip y) #x20222222)))

; We want to prove following:
(assert  (forall ((x Flow)) (=> (P x) (exists ((y Flow)) (and (R x y) (Q y)) ) ) ) )

; So what is the representation as (un)sat formula?
; vvvv

; ^^^^

(check-sat)
(get-m  odel)
(get-info :all-statistics)
