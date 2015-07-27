(declare-datatypes () ((Flow (mk-flow (srcip Int) (srcpn Int) (dstip Int) (dstpn Int) (proto Int)))))

(define-fun assert_flow ((f Flow)) Bool
	(and (>= (srcip f) 0)(<= (srcip f) 4294967295)
	     (>= (dstip f) 0)(<= (dstip f) 4294967295)
	     (>= (srcpn f) 0)(<= (srcpn f) 65535)
	     (>= (dstpn f) 0)(<= (dstpn f) 65535)
	     (>= (proto f) 0)(<= (proto f) 65535)
	)
)

; unsat ~ Flow \subseteq Filter:
(define-fun Includes ((filter Bool)(flow Bool)) Bool (and flow (not filter)))

; unsat ~ Flow \cap Filter = \empty
(define-fun Disjoint ((filter Bool)(flow Bool)) Bool (and flow filter))


(define-fun f_1 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 4294967295)
     (>= (dstip f) 1) (<= (dstip f) 4294967295)
     (>= (srcpn f) 1) (<= (srcpn f) 65535)
     (>= (dstpn f) 1) (<= (dstpn f) 65535)
     (>= (proto f) 1) (<= (proto f) 255)
))

(define-fun T_1 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_2 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_3 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_4 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_5 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_6 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_7 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)

(define-fun F_1 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_2 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_3 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_4 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_5 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_6 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_7 ((x Flow)) Bool
  (or(f_1 x))
)

(define-fun R ((x Flow)(y Flow)) Bool (exists ((z1 Flow)(z2 Flow)(z3 Flow)(z4 Flow)(z5 Flow)(z6 Flow)(z7 Flow)
                                              )
                                              (and (T_1 x z1) (F_1 z1) (T_2 z1 z2) (F_2 z2)(T_3 z2 z3) (F_3 z3)(T_4 z3 z4) (F_4 z4)(T_5 z4 z5) (F_5 z5)(T_6 z5 z6) (F_6 z6)(T_7 z6 z7) (F_7 z7) 
                                              )
                                      )
)
(define-fun P ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun Q ((x Flow)) Bool
  (or(f_1 x))
)
(assert (forall ((x Flow)) (exists ((y Flow)) (=> (P x) (Includes (R x y) (Q y)) ) ) ) )
(check-sat)
(get-info :all-statistics)
