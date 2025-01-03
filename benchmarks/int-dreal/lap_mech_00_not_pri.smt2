; First example. We know it's differentially private, but the
; tool can't determine this (by an unsat result) since the integrals are equal.
(set-logic QF_NRA)

(declare-fun eps () Real)
(assert (>= eps 0.1))
(assert (<= eps 1))

(declare-fun a () Real)
(assert (= a 1))

(declare-fun b () Real)
(assert (= b 2))

(assert 
 (not
    (> (integral a b
            (lambda (x Real)
                (exp (- (* eps (abs x))))))
        (* (exp eps)
            (integral a b
                (lambda (x Real)
                    (exp (- (* eps (abs (+ x 1)))))))
            )
        )))

(check-sat) ; Is delta-sat
(exit)
