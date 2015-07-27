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
(define-fun T_8 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_9 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_10 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_11 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_12 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_13 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_14 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_15 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_16 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_17 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_18 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_19 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_20 ((x Flow)(y Flow)) Bool
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
(define-fun F_8 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_9 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_10 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_11 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_12 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_13 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_14 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_15 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_16 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_17 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_18 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_19 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_20 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun R ((x Flow)(y Flow)) Bool (exists ((z1 Flow)(z2 Flow)(z3 Flow)(z4 Flow)(z5 Flow)(z6 Flow)(z7 Flow)(z8 Flow)(z9 Flow)(z10 Flow)(z11 Flow)(z12 Flow)(z13 Flow)(z14 Flow)(z15 Flow)(z16 Flow)(z17 Flow)(z18 Flow)(z19 Flow)) (and (T_1 x z1) (F_1 z1) (T_2 z1 z2) (F_2 z2)(T_3 z2 z3) (F_3 z3)(T_4 z3 z4) (F_4 z4)(T_5 z4 z5) (F_5 z5)(T_6 z5 z6) (F_6 z6)(T_7 z6 z7) (F_7 z7)(T_8 z7 z8) (F_8 z8)(T_9 z8 z9) (F_9 z9)(T_10 z9 z10) (F_10 z10)(T_11 z10 z11) (F_11 z11)(T_12 z11 z12) (F_12 z12)(T_13 z12 z13) (F_13 z13)(T_14 z13 z14) (F_14 z14)(T_15 z14 z15) (F_15 z15)(T_16 z15 z16) (F_16 z16)(T_17 z16 z17) (F_17 z17)(T_18 z17 z18) (F_18 z18)(T_19 z18 z19) (F_19 z19)(T_20 z19 y))))
(define-fun P ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun Q ((x Flow)) Bool
  (or(f_1 x))
)
(assert (forall ((x Flow)) (exists ((y Flow)) (=> (P x) (Includes (R x y) (Q y)) ) ) ) )
(check-sat)
(get-info :all-statistics)
