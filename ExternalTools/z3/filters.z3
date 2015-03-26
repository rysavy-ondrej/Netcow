(declare-fun srcip () Int)
(declare-fun dstip () Int)
(declare-fun srcpn () Int)
(declare-fun dstpn () Int)
; Firewall
(assert
(or
  ; Flow(*)
  (and (>= srcip 0) (<= srcip 100)
       (>= dstip 0)  (<= dstip 100)
       (>= srcpn 0)  (<= srcpn 100)
       (>= dstpn 0)  (<= dstpn 100))
  ; Flow(f1)
  (and (>= srcip 10) (<= srcip 20)
       (>= dstip 40) (<= dstip 40)
       (>= srcpn 0)  (<= srcpn 100)
       (>= dstpn 80) (<= dstpn 80))
)
)
; Test flow:
(assert 
  (and (>= srcip 5) (<= srcip 5)
       (>= dstip 5) (<= dstip 5)
       (>= srcpn 5)  (<= srcpn 5)
       (>= dstpn 5) (<= dstpn 5))
)
(check-sat)
(get-model)
