; Laplace mechanism accuracy. First formulation, with double integral.
; k == 2.
(set-logic QF_NRA)

(declare-fun eps () Real)
(assert (>= eps 0.1))
(assert (<= eps 1))

(declare-fun delta () Real)
(assert (>= delta 0.001))
(assert (<= delta 1))

(assert 
 (not
    (>  (* (/ (* eps eps) 4)
            (integral (- (* (/ 1 eps) (log (/ 2 delta))))
                      (+ (* (/ 1 eps) (log (/ 2 delta))))
                (lambda (x Real)
                    (integral   (- (* (/ 1 eps) (log (/ 2 delta))))
                                (+ (* (/ 1 eps) (log (/ 2 delta))))
                            (lambda (y Real)
                                    (* (exp (- (* eps (abs x))))
                                       (exp (- (* eps (abs y))))
                                    )
                                    ))
                        )))
        (- 1 delta))))

(check-sat)
(exit)
