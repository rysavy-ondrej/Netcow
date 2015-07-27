(set-option :produce-unsat-cores true)
(set-option :produce-models false)

; unsat ~ Flow \subseteq Filter:
(define-fun Includes ((filter Bool)(flow Bool)) Bool (and flow (not filter)))

; unsat ~ Flow \cap Filter = \empty
(define-fun Disjoint ((filter Bool)(flow Bool)) Bool (and flow filter))

(define-fun f0 ((x Int)) Bool (and (>= x 0)(<= x 40) ) )
(define-fun f1 ((x Int)) Bool (or (and (>= x 10)(<= x 20)) (and (>= x 30)(<= x 40))) )
(define-fun f2 ((x Int)) Bool (or (and (>= x 25)(<= x 40)) (and (>= x 50)(<= x 80))) )

(define-fun t1 ((x1 Int)(x2 Int)) Bool (= x1 x2) )
(define-fun t2 ((x1 Int)(x2 Int)) Bool (= x2 (+ x1 10)))



(define-fun t3 ((x1 Int)(x2 Int)) Bool (and (=> (>= x1 10) (<= x1 15) (= x2 30))
                                            (=> (<  x1 10)            (= x1 x2))
                                            (=> (>  x1 15)            (= x1 x2))
                                       )
) 

(define-fun p1 ((x Int)) Bool (and (>= x 7)(<= x 13)) )
(define-fun p2 ((x Int)) Bool (and (>= x 14)(<= x 15)) )
(define-fun p3 ((x Int)) Bool (and (>= x 24)(<= x 25)) )
(define-fun p4 ((x Int)) Bool (and (= x 40)) )

(define-fun highpass ((x Int)(y Int)) Bool (and (=> (> x 20)(= y x))
										   (=> (< x 20) (= y 0))
								      )
)

(define-fun midpass ((x Int)(y Int)) Bool (and (=> (>= x 10)(<= x 30)(= y x))
										   (=> (< x 10) (= y 0))
										   (=> (> x 30) (= y 0))
								      )
)

(define-fun Join ((t1 (Int Int Bool)) (f1 (Int Bool)) (f2 (Int Bool))(t2 (Int Int Bool)) (x Int)(y Int) ) Bool 
	(exists ((z Int)) (and (t1 x z) (f1 z) (f2 z) (t2 z y)))
)

(define-fun RR ((x Int)(y Int)) Bool (exists ((z1 Int)(z2 Int))
										(and (highpass x z1)(f0 z1)(f0 z1)(midpass z1 z2)(f0 z2)(f0 z2)(highpass z2 y)
										)
                                     )
)

; 
(assert (forall ((y Int)) (exists ((x Int)) (=> (= y 0) (and (RR x y) (p2 x )) ) ) ) )
; assume x -> ensure y
(assert (forall ((x Int)) (exists ((y Int)) (=> (p2 x) (and (RR x y) (= y 0)) ) ) ) )


(check-sat)
;(get-unsat-core)
(get-info :all-statistics)