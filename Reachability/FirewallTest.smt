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

