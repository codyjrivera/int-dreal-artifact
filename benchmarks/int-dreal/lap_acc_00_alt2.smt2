; Laplace mechanism accuracy. Second formulation, with square of integral
; k == 2.
(set-logic QF_NRA)

(declare-fun eps () Real)
(assert (>= eps 0.1))
(assert (<= eps 1))

(declare-fun delta () Real)
(assert (> delta 0.001))
(assert (<= delta 1))

(assert 
 (not
    (>  (* (/ (* eps eps) 4)
            (pow 
                (integral (- (* (/ 1 eps) (log (/ 2 delta))))
                          (+ (* (/ 1 eps) (log (/ 2 delta))))
                  (lambda (x Real)
                        (exp (- (* eps (abs x))))))
                2))
        (- 1 delta))))

(check-sat)
(exit)
