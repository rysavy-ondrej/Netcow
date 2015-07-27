(declare-datatypes () ((Flow (mk-flow (srcip (_ BitVec 32)) (srcpn (_ BitVec 16)) (dstip (_ BitVec 32)) (dstpn (_ BitVec 16)) (proto (_ BitVec 16))))))

; unsat ~ Flow \subseteq Filter:
(define-fun Includes ((filter Bool)(flow Bool)) Bool (and flow (not filter)))

; unsat ~ Flow \cap Filter = \empty
(define-fun Disjoint ((filter Bool)(flow Bool)) Bool (and flow filter))


(define-fun f_0 ((f Flow)) Bool
(and (bvuge (srcip f) #x00000000) (bvule (srcip f) #xffffffff)
     (bvuge (dstip f) #x00000000) (bvule (dstip f) #xffffffff)
     (bvuge (srcpn f) #x0000) (bvule (srcpn f) #xffff)
     (bvuge (dstpn f) #x0000) (bvule (dstpn f) #xffff)
     (bvuge (proto f) #x0000) (bvule (proto f) #xffff)
))


(define-fun f_1 ((f Flow)) Bool
(and (bvuge (srcip f) #x00000001) (bvule (srcip f) #xffffffff)
     (bvuge (dstip f) #x00000001) (bvule (dstip f) #xffffffff)
     (bvuge (srcpn f) #x0001) (bvule (srcpn f) #xffff)
     (bvuge (dstpn f) #x0001) (bvule (dstpn f) #xffff)
     (bvuge (proto f) #x0001) (bvule (proto f) #x00ff)
))

(define-fun f_2 ((f Flow)) Bool
(and (bvuge (srcip f) #x00000001) (bvule (srcip f) #x00ffffff)
     (bvuge (dstip f) #x00000001) (bvule (dstip f) #x00ffffff)
     (bvuge (srcpn f) #x0001) (bvule (srcpn f) #xffff)
     (bvuge (dstpn f) #x0001) (bvule (dstpn f) #xffff)
     (bvuge (proto f) #x0001) (bvule (proto f) #x00ff)
))

(define-fun f_3 ((f Flow)) Bool
(and (bvuge (srcip f) #x00ff0000) (bvule (srcip f) #x00ffffff)
     (bvuge (dstip f) #x00ff0000) (bvule (dstip f) #x00ffffff)
     (bvuge (srcpn f) #x0001) (bvule (srcpn f) #xffff)
     (bvuge (dstpn f) #x0001) (bvule (dstpn f) #xffff)
     (bvuge (proto f) #x0001) (bvule (proto f) #x00ff)
))

(define-fun T_1 ((x Flow)(y Flow)) Bool
  (or (=> (f_2 x) (= y x)) (=> (! (f_2 x)) (= y (mk-flow #x00000000 #x0000 #x00000000 #x0000 #x0000 ) ) ) )
)

(define-fun T_2 ((x Flow)(y Flow)) Bool
  (or (=> (f_1 x) (= y x)) (=> (! (f_1 x)) (= y (mk-flow #x00000000 #x0000 #x00000000 #x0000 #x0000 ) ) ) )
)

(define-fun T_3 ((x Flow)(y Flow)) Bool
  (or (=> (f_1 x) (= y x)) (=> (! (f_1 x)) (= y (mk-flow #x00000000 #x0000 #x00000000 #x0000 #x0000 ) ) ) )
)

(define-fun T_4 ((x Flow)(y Flow)) Bool
  (or (=> (f_1 x) (= y x)) (=> (! (f_1 x)) (= y (mk-flow #x00000000 #x0000 #x00000000 #x0000 #x0000 ) ) ) )
)

(define-fun T_5 ((x Flow)(y Flow)) Bool
  (or (=> (f_1 x) (= y x)) (=> (! (f_1 x)) (= y (mk-flow #x00000000 #x0000 #x00000000 #x0000 #x0000 ) ) ) )
)

(define-fun T_6 ((x Flow)(y Flow)) Bool
  (or (=> (f_1 x) (= y x)) (=> (! (f_1 x)) (= y (mk-flow #x00000000 #x0000 #x00000000 #x0000 #x0000 ) ) ) )
)

(define-fun F_permit_all ((x Flow)) Bool (f_0 x))

(define-fun F_1 ((x Flow)) Bool
  (or (f_1 x))
)
(define-fun F_2 ((x Flow)) Bool
  (or (f_1 x))
)
(define-fun F_3 ((x Flow)) Bool
  (or (f_1 x))
)
(define-fun F_4 ((x Flow)) Bool
  (or (f_1 x))
)

(define-fun F_5 ((x Flow)) Bool
  (or (f_1 x))
)

(define-fun F_6 ((x Flow)) Bool
  (or (f_1 x))
)

(define-fun R ((x Flow)(y Flow)) Bool (exists ((z1 Flow)(z2 Flow)(z3 Flow)(z4 Flow)(z5 Flow))
                                              (and (F_1 x)
                                                   (T_1 x z1) 
                                                   (F_1 z1) 
                                                   (T_2 z1 z2) 
                                                   (F_2 z2)
                                                   (T_3 z2 z3)
                                                   (F_3 z3)
                                                   (T_4 z3 z4)
                                                   (F_4 z4)
                                                   (T_5 z4 y)
                                                   (F_5 y)
                                              )
                                      )
)

(define-fun P ((x Flow)) Bool
  (or(f_1 x))
)

(define-fun Q ((x Flow)) Bool
  (or(f_3 x))
)

(assert  (forall ((x Flow)) (exists ((y Flow)) (=> (P x) (Includes  (R x y) (Q y)) ) ) ) )
(check-sat)
(get-model)
(get-info :all-statistics)
