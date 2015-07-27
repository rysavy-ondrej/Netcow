
(declare-datatypes () ((Flow (mk-flow (srcip Int) (srcpn Int) (dstip Int) (dstpn Int) (proto Int)))))

(define-fun assert_flow ((f Flow)) Bool
	(and (>= (srcip f) 0)(<= (srcip f) 4294967295)
	     (>= (dstip f) 0)(<= (dstip f) 4294967295)
	     (>= (srcpn f) 0)(<= (srcpn f) 65535)
	     (>= (dstpn f) 0)(<= (dstpn f) 65535)
	     (>= (proto f) 0)(<= (proto f) 65535)
	)
)

(declare-const x1 Flow)
(assert (assert_flow x1))
(declare-const x2 Flow)
(assert (assert_flow x2))
(declare-const x3 Flow)
(assert (assert_flow x3))

; unsat ~ Flow \subseteq Filter:
(define-fun Includes ((filter Bool)(flow Bool)) Bool (and flow (not filter)))

; unsat ~ Flow \cap Filter = \empty
(define-fun Disjoint ((filter Bool)(flow Bool)) Bool (and flow filter))


; Flow(*)
(define-fun f_any ((f Flow)) Bool
  (and (>= (srcip f) 0) (<= (srcip f) 4294967295)
       (>= (dstip f) 0) (<= (dstip f) 4294967295)
       (>= (srcpn f) 0) (<= (srcpn f) 65535)
       (>= (dstpn f) 0) (<= (dstpn f) 65535)
	   (>= (proto f) 0) (<= (proto f) 65535)
  )
)

(define-fun f_http ((f Flow)) Bool
  (and 
       (>= (dstpn f) 80) (<= (dstpn f) 80)
	   (>= (proto f) 80) (<= (proto f) 80)
  )
)

(define-fun f_web1 ((f Flow)) Bool
	(and (>= (srcip f) 10)(<= (srcip f) 19)
		 (>= (dstip f) 0)(<= (dstip f) 9)
		 (>= (dstpn f) 80)(<= (dstpn f) 80)
		 (>= (proto f) 80)(<= (proto f) 80)
	)
)
(define-fun f_web2 ((f Flow)) Bool
	(and (>= (srcip f) 10)(<= (srcip f) 19)
		 (>= (dstip f) 20)(<= (dstip f) 4294967295)
		 (>= (dstpn f) 80)(<= (dstpn f) 80)
		 (>= (proto f) 80)(<= (proto f) 80)
	)
)
; Flow("web-traffic")
(define-fun f_web ((f Flow)) Bool
	(or	(f_web1 f) 
	    (f_web2 f)
	)
) 

(define-fun t_id ((f1 Flow)(f2 Flow)) Bool
	(and (= f1 f2)
	)
)


; f_web @ (f_any -> t_id -> f_http) @ f_web
(assert (and (t_id x1 x2) (t_id x2 x3)))
(assert (Includes 
	; FILTERS
	(and (f_any x1) 		 
		 (f_http x2)
		 (f_http x3)	
	) 
	
	; FLOWS
	(and (f_web x1)
		 (f_web x3))
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
