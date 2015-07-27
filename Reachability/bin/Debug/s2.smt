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
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_2 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_3 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_4 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_5 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_6 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_7 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_8 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_9 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_10 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_11 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_12 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_13 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_14 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_15 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_16 ((f Flow)) Bool
(and (>= (srcip f) 1) (<= (srcip f) 2147483647)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_17 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_18 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_19 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_20 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_21 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_22 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_23 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_24 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 1) (<= (dstip f) 2147483647)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_25 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_26 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_27 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_28 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 1) (<= (srcpn f) 32767)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_29 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_30 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 1) (<= (dstpn f) 32767)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun f_31 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 1) (<= (proto f) 127)
))

(define-fun f_32 ((f Flow)) Bool
(and (>= (srcip f) 2147483648) (<= (srcip f) 4294967294)
     (>= (dstip f) 2147483648) (<= (dstip f) 4294967294)
     (>= (srcpn f) 32768) (<= (srcpn f) 65534)
     (>= (dstpn f) 32768) (<= (dstpn f) 65534)
     (>= (proto f) 128) (<= (proto f) 254)
))

(define-fun T_1 ((x Flow)(y Flow)) Bool
  (or (and (f_26 x) (f_19 y)))
)
(define-fun T_2 ((x Flow)(y Flow)) Bool
  (or (and (f_7 x) (f_13 y)))
)
(define-fun F_1 ((x Flow)) Bool
  (or(f_8 x))
)
(define-fun F_2 ((x Flow)) Bool
  (or(f_22 x))
)
(define-fun R ((x Flow)(y Flow)) Bool (exists ((z1 Flow)) (and (T_1 x z1) (F_1 z1) (T_2 z1 y))))
(define-fun P ((x Flow)) Bool
  (or(f_7 x))
)
(define-fun Q ((x Flow)) Bool
  (or(f_5 x))
)
(assert (forall ((x Flow)) (exists ((y Flow)) (=> (P x) (Disjoint (R x y) (Q y)) ) ) ) )
(check-sat)
(get-info :all-statistics)
