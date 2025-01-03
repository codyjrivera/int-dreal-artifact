; Laplace mechanism accuracy. k == 4.
(set-logic QF_NRA)

(declare-fun k () Real)
(assert (= k 4))

(declare-fun eps () Real)
(assert (>= eps 0.1))
(assert (<= eps 1))

(declare-fun delta () Real)
(assert (> delta 0.001))
(assert (<= delta 1))

(assert 
 (not
    (>  (* (/ (pow eps k) (pow 2 k))
            (* 
                (integral (- (* (/ 1 eps) (log (/ k delta))))
                          (+ (* (/ 1 eps) (log (/ k delta))))
                  (lambda (x Real)
                        (exp (- (* eps (abs x))))))

                (integral (- (* (/ 1 eps) (log (/ k delta))))
                          (+ (* (/ 1 eps) (log (/ k delta))))
                  (lambda (x Real)
                        (exp (- (* eps (abs x))))))

                (integral (- (* (/ 1 eps) (log (/ k delta))))
                          (+ (* (/ 1 eps) (log (/ k delta))))
                  (lambda (x Real)
                        (exp (- (* eps (abs x))))))

                (integral (- (* (/ 1 eps) (log (/ k delta))))
                          (+ (* (/ 1 eps) (log (/ k delta))))
                  (lambda (x Real)
                        (exp (- (* eps (abs x))))))
                ))
        (- 1 delta))))

(check-sat)
(exit)
