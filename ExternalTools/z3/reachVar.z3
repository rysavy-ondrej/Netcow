(declare-const srcip Int)
(declare-const dstip Int)
(declare-const srcpn Int)
(declare-const dstpn Int)
(declare-const proto Int)

(assert (and (>= srcip 0)(<= srcip 4294967295)))
(assert (and (>= dstip 0)(<= dstip 4294967295)))
(assert (and (>= srcpn 0)(<= srcpn 65535)))
(assert (and (>= dstpn 0)(<= dstpn 65535)))
(assert (and (>= proto 0)(<= proto 65535)))

(declare-const srcip1 Int)
(declare-const dstip1 Int)
(declare-const srcpn1 Int)
(declare-const dstpn1 Int)
(declare-const proto1 Int)

(assert (and (>= srcip1 0)(<= srcip1 4294967295)))
(assert (and (>= dstip1 0)(<= dstip1 4294967295)))
(assert (and (>= srcpn1 0)(<= srcpn1 65535)))
(assert (and (>= dstpn1 0)(<= dstpn1 65535)))
(assert (and (>= proto1 0)(<= proto1 65535)))

(declare-const srcip2 Int)
(declare-const dstip2 Int)
(declare-const srcpn2 Int)
(declare-const dstpn2 Int)
(declare-const proto2 Int)

(assert (and (>= srcip2 0)(<= srcip2 4294967295)))
(assert (and (>= dstip2 0)(<= dstip2 4294967295)))
(assert (and (>= srcpn2 0)(<= srcpn2 65535)))
(assert (and (>= dstpn2 0)(<= dstpn2 65535)))
(assert (and (>= proto2 0)(<= proto2 65535)))

; unsat ~ Flow \subseteq Filter:
(define-fun Includes ((filter Bool)(flow Bool)) Bool (and flow (not filter)))

; unsat ~ Flow \cap Filter = \empty
(define-fun Disjoint ((filter Bool)(flow Bool)) Bool (and flow filter))


; Flow(*)
(define-fun f_any ((sa Int)(sp Int)(da Int)(dp Int)(pt Int)) Bool
  (and (>= sa 0) (<= sa 4294967295)
       (>= da 0) (<= da 4294967295)
       (>= sp 0) (<= sp 65535)
       (>= dp 0) (<= dp 65535)
	   (>= pt 0) (<= pt 65535)
  )
)

(define-fun f_http ((sa Int)(sp Int)(da Int)(dp Int)(pt Int)) Bool
  (and 
       (>= dp 80) (<= dp 80)
	   (>= pt 80) (<= pt 80)
  )
)

(define-fun f_web1 ((sa Int)(sp Int)(da Int)(dp Int)(pt Int)) Bool
	(and (>= sa 10)(<= sa 19)
		 (>= da 0)(<= da 9)
		 (>= dp 80)(<= dp 80)
		 (>= pt 80)(<= pt 80)
	)
)
(define-fun f_web2 ((sa Int)(sp Int)(da Int)(dp Int)(pt Int)) Bool
	(and (>= sa 10)(<= sa 19)
		 (>= da 20)(<= da 4294967295)
		 (>= dp 80)(<= dp 80)
		 (>= pt 80)(<= pt 80)
	)
)
; Flow("web-traffic")
(define-fun f_web ((sa Int)(sp Int)(da Int)(dp Int)(pt Int)) Bool
	(or	(f_web1 sa sp da dp pt) 
	    (f_web2 sa sp da dp pt)
	)
) 

(define-fun t_id ((sa1 Int)(sp1 Int)(da1 Int)(dp1 Int)(pt1 Int)(sa2 Int)(sp2 Int)(da2 Int)(dp2 Int)(pt2 Int)) Bool
	(and (= sa1 sa2)
		 (= da1 da2)
		 (= sp1 sp2)
		 (= dp1 dp2)
		 (= pt1 pt2)
	)
)


; f_web @ (f_any -> t_id -> f_http) @ f_web

(assert (t_id srcip1 srcpn1 dstip1 dstpn1 proto1 srcip2 srcpn2 dstip2 dstpn2 proto2))

(assert (Includes 
	(and (f_any srcip1 srcpn1 dstip1 dstpn1 proto1) 		 
		 (f_http srcip2 srcpn2 dstip2 dstpn2 proto2) ) 

	(and (f_web srcip1 srcpn1 dstip1 dstpn1 proto1)
		 (f_web srcip2 srcpn2 dstip2 dstpn2 proto2))
))


;(assert (Disjoint (f_web1 srcip srcpn dstip dstpn proto) (f_web2 srcip srcpn dstip dstpn proto)))


(check-sat)
(get-model)
; Single dimension only:
;(declare-fun x () Int)
;(define-fun Filter () Bool (or (and (>= x 10)(<= x 20)) (and (>= x 30)(<= x 40))) )
;(define-fun Flow1 () Bool  (and (>= x 15)(<= x 20)) )
;(define-fun Flow2 () Bool  (and (>= x 21)(<= x 29)) )
;(assert (Includes Filter Flow1))
;(assert (Disjoint Filter Flow2))
