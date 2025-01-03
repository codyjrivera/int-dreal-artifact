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

                                (integral (- k) k
                                    (lambda (x6 Real)
                                        (exp (- (/ (* (- x6 0) (- x6 0) eps eps 7) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x7 Real)
                                        (exp (- (/ (* (- x7 0) (- x7 0) eps eps 8) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x8 Real)
                                        (exp (- (/ (* (- x8 0) (- x8 0) eps eps 9) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x9 Real)
                                        (exp (- (/ (* (- x9 0) (- x9 0) eps eps 10) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x10 Real)
                                        (exp (- (/ (* (- x10 0) (- x10 0) eps eps 11) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x11 Real)
                                        (exp (- (/ (* (- x11 0) (- x11 0) eps eps 12) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x12 Real)
                                        (exp (- (/ (* (- x12 0) (- x12 0) eps eps 13) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x13 Real)
                                        (exp (- (/ (* (- x13 0) (- x13 0) eps eps 14) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x14 Real)
                                        (exp (- (/ (* (- x14 0) (- x14 0) eps eps 15) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x15 Real)
                                        (exp (- (/ (* (- x15 0) (- x15 0) eps eps 16) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x16 Real)
                                        (exp (- (/ (* (- x16 0) (- x16 0) eps eps 17) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x17 Real)
                                        (exp (- (/ (* (- x17 0) (- x17 0) eps eps 18) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x18 Real)
                                        (exp (- (/ (* (- x18 0) (- x18 0) eps eps 19) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x19 Real)
                                        (exp (- (/ (* (- x19 0) (- x19 0) eps eps 20) (* 2 4))))
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