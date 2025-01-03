(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun eps () Real)
(assert (>= eps 0.10))
(assert (<= eps 0.90))

(declare-fun k () Real)
(assert (= k 24))

(assert
   (not
    (<=
        (+
        (* (/
                1
                (*
                    2
                    pi
                    (pow (sqrt (/ 4 (* eps eps))) 3)
                    (sqrt (* 2 pi))))

            (integral (- k) k
            (lambda (z Real)
            (* (integral (- 1 k) z
            (lambda (y Real)
                (exp (- (/ (* (- y 1) (- y 1) eps eps)
                               (* 2 4))))))

            (integral (- 0 k) z
            (lambda (x Real)
                (exp (- (/ (* (- x 0) (- x 0) eps eps)
                               (* 2 4))))

                    ))

                    (exp (- (/ (* z z eps eps)
                               (* 2 4))))

                    )

                    ))
            )
        (/ 3 100)
        )
        (+
        (* (/
                1
                (*
                    2
                    pi
                    (pow (sqrt (/ 4 (* eps eps))) 3)
                    (sqrt (* 2 pi))))

            (integral (- k) k
            (lambda (z Real)
            (* (integral (- 0 k) z
            (lambda (y Real)
                (exp (- (/ (* (- y 0) (- y 0) eps eps)
                               (* 2 4))))))

            (integral (- 1 k) z
            (lambda (x Real)
                  (exp (- (/ (* (- x 1) (- x 1) eps eps)
                               (* 2 4))))

                    ))

                    (exp (- (/ (* z z eps eps)
                               (* 2 4))))

                    )

                    ))
            )
        (/ 1 8)
        )
    )))

(check-sat) ; should be unsat
(exit)
