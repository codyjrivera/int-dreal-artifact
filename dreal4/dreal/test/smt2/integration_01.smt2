
;; Essentially, proves that forall z \in [5, 100], 1/2 z^2 < z.

(set-logic QF_NRA)
(declare-fun z () Real)
(assert (>= z 5))
(assert (<= z 100))
(assert 
    (>= 
        (integral 0 z 
            (lambda (x Real) x)) 
        (integral 0 z 
            (lambda (x Real) (* 2 x)))))
(check-sat) ; should be unsat
(exit)

