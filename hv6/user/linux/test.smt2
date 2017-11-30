(declare-fun q () Bool)
(declare-fun p () Bool)
(assert
 (=> p q))
(assert
 p)
(assert
 (not q))
(check-sat)
