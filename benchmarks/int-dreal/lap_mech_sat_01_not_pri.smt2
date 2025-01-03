; Second example. We know the inequality is false, so the
; negation must be delta-sat.
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
        (* (exp (/ eps 2))
            (integral a b
                (lambda (x Real)
                    (exp (- (* eps (abs (+ x 1)))))))
            )
        )))

(check-sat) ; Should be delta-sat
(exit)
