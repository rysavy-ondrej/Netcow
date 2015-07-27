(declare-datatypes () ((Flow (mk-flow (srcip Int) (srcpn Int) (dstip Int) (dstpn Int) (proto Int)))))

(define-fun assert_flow ((f Flow)) Bool
	(and (>= (srcip f) 0)(<= (srcip f) 4294967295)
	     (>= (dstip f) 0)(<= (dstip f) 4294967295)
	     (>= (srcpn f) 0)(<= (srcpn f) 65535)
	     (>= (dstpn f) 0)(<= (dstpn f) 65535)
	     (>= (proto f) 0)(<= (proto f) 65535)
	)
)

(define-fun zero_flow ((f Flow)) Bool
	(and (>= (srcip f) 0)(<= (srcip f) 0)
	     (>= (dstip f) 0)(<= (dstip f) 0)
	     (>= (srcpn f) 0)(<= (srcpn f) 0)
	     (>= (dstpn f) 0)(<= (dstpn f) 0)
	     (>= (proto f) 0)(<= (proto f) 0)
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

(define-fun f_2 ((f Flow)) Bool
(and (>= (srcip f) 10) (<= (srcip f) 1000)
     (>= (dstip f) 0) (<= (dstip f) 4294967295)
     (>= (srcpn f) 0) (<= (srcpn f) 65535)
     (>= (dstpn f) 0) (<= (dstpn f) 65535)
     (>= (proto f) 0) (<= (proto f) 255)
))

(define-fun f_3 ((f Flow)) Bool
(and (>= (srcip f) 2000) (<= (srcip f) 3000)
     (>= (dstip f) 0) (<= (dstip f) 4294967295)
     (>= (srcpn f) 0) (<= (srcpn f) 65535)
     (>= (dstpn f) 0) (<= (dstpn f) 65535)
     (>= (proto f) 0) (<= (proto f) 255)
))

(define-fun T_1 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun T_2 ((x Flow)(y Flow)) Bool
  (or (and (f_1 x) (f_1 y)))
)
(define-fun F_1 ((x Flow)) Bool
  (or(f_1 x))
)
(define-fun F_2 ((x Flow)) Bool
  (or(f_1 x))
)

(declare-const xi Flow)
(assert (assert_flow xi))
(declare-const x2 Flow)
(assert (assert_flow x2))
(declare-const x3 Flow)
(assert (assert_flow x3))
(declare-const xo Flow)
(assert (assert_flow xo))

(assert (and (T_1 xi x2) (F_1 x2)  (T_2 x2 xo) ))

(define-fun P ((x Flow)) Bool
  (f_2 x)
)

(define-fun Q ((x Flow)) Bool
  (f_3 x)
)

;(assert (forall ((x Flow)) (exists ((y Flow)) (=> (P x) (Includes (R x y) (Q y)) ) ) ) )

; P ==> Q
(assert (=> (P xi) (Q xo)))
;(assert (not (=> (P xi) (Q xo))))

; P =/=> Q
;(assert (not (=> (P xi) (not (Q xo))) ))

(check-sat)
(get-info :all-statistics)
