(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun eps () Real)
(assert (>= eps 0.50))
(assert (<= eps 0.60))

(declare-fun k () Real)
(assert (= k 1))

(assert
    (not
        (<=
            (+
                (* 
                    (/
                        1
                        (* 
                            2 
                            pi 
                            (pow (sqrt (/ 4 (* eps eps))) 3) 
                            (sqrt (* 2 pi))
                        )
                    )
                    (+ 
                        (integral (- k) k
                            (lambda (y Real)
                                (exp (- (/ (* (- y 1) (- y 1)) (* eps eps 2 4))))
                            )
                        )
                        
                                (integral (- k) k
                                    (lambda (x1 Real)
                                        (exp (- (/ (* (- x1 0) (- x1 0) eps eps 2) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x2 Real)
                                        (exp (- (/ (* (- x2 0) (- x2 0) eps eps 3) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x3 Real)
                                        (exp (- (/ (* (- x3 0) (- x3 0) eps eps 4) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x4 Real)
                                        (exp (- (/ (* (- x4 0) (- x4 0) eps eps 5) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x5 Real)
                                        (exp (- (/ (* (- x5 0) (- x5 0) eps eps 6) (* 2 4))))
                                    )
                                )

                    )
                )
                
            )
            (/ 1 100)
        )
    )
)

(check-sat) ; should be unsat
(exit)