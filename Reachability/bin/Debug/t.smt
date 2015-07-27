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
  (or (and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y)))
)
(define-fun T_2 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y)))
)
(define-fun T_3 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y))(and (f_1 x) (f_1 y)))
)
(define-fun F_1 ((x Flow)) Bool
  (or(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x))
)
(define-fun F_2 ((x Flow)) Bool
  (or(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x))
)
(define-fun F_3 ((x Flow)) Bool
  (or(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x))
)
(define-fun R ((x Flow)(y Flow)) Bool (exists ((z1 Flow)(z2 Flow)) (and (T_1 x z1) (F_1 z1) (T_2 z1 z2) (F_2 z2)(T_3 z2 y))))
(define-fun P ((x Flow)) Bool
  (or(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x))
)
(define-fun Q ((x Flow)) Bool
  (or(f_1 x)(f_1 x)(f_1 x)(f_1 x)(f_1 x))
)
(assert (forall ((x Flow)) (exists ((y Flow)(z Flow)) (=> (P x) (Disjoint (and (T_1 x z)(T_2 z y) ) (Q y)) ) ) ) )
(check-sat)
(get-info :all-statistics)
