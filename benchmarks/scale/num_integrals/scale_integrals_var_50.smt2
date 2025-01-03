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

                                (integral (- k) k
                                    (lambda (x20 Real)
                                        (exp (- (/ (* (- x20 0) (- x20 0) eps eps 21) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x21 Real)
                                        (exp (- (/ (* (- x21 0) (- x21 0) eps eps 22) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x22 Real)
                                        (exp (- (/ (* (- x22 0) (- x22 0) eps eps 23) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x23 Real)
                                        (exp (- (/ (* (- x23 0) (- x23 0) eps eps 24) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x24 Real)
                                        (exp (- (/ (* (- x24 0) (- x24 0) eps eps 25) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x25 Real)
                                        (exp (- (/ (* (- x25 0) (- x25 0) eps eps 26) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x26 Real)
                                        (exp (- (/ (* (- x26 0) (- x26 0) eps eps 27) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x27 Real)
                                        (exp (- (/ (* (- x27 0) (- x27 0) eps eps 28) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x28 Real)
                                        (exp (- (/ (* (- x28 0) (- x28 0) eps eps 29) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x29 Real)
                                        (exp (- (/ (* (- x29 0) (- x29 0) eps eps 30) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x30 Real)
                                        (exp (- (/ (* (- x30 0) (- x30 0) eps eps 31) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x31 Real)
                                        (exp (- (/ (* (- x31 0) (- x31 0) eps eps 32) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x32 Real)
                                        (exp (- (/ (* (- x32 0) (- x32 0) eps eps 33) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x33 Real)
                                        (exp (- (/ (* (- x33 0) (- x33 0) eps eps 34) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x34 Real)
                                        (exp (- (/ (* (- x34 0) (- x34 0) eps eps 35) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x35 Real)
                                        (exp (- (/ (* (- x35 0) (- x35 0) eps eps 36) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x36 Real)
                                        (exp (- (/ (* (- x36 0) (- x36 0) eps eps 37) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x37 Real)
                                        (exp (- (/ (* (- x37 0) (- x37 0) eps eps 38) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x38 Real)
                                        (exp (- (/ (* (- x38 0) (- x38 0) eps eps 39) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x39 Real)
                                        (exp (- (/ (* (- x39 0) (- x39 0) eps eps 40) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x40 Real)
                                        (exp (- (/ (* (- x40 0) (- x40 0) eps eps 41) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x41 Real)
                                        (exp (- (/ (* (- x41 0) (- x41 0) eps eps 42) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x42 Real)
                                        (exp (- (/ (* (- x42 0) (- x42 0) eps eps 43) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x43 Real)
                                        (exp (- (/ (* (- x43 0) (- x43 0) eps eps 44) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x44 Real)
                                        (exp (- (/ (* (- x44 0) (- x44 0) eps eps 45) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x45 Real)
                                        (exp (- (/ (* (- x45 0) (- x45 0) eps eps 46) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x46 Real)
                                        (exp (- (/ (* (- x46 0) (- x46 0) eps eps 47) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x47 Real)
                                        (exp (- (/ (* (- x47 0) (- x47 0) eps eps 48) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x48 Real)
                                        (exp (- (/ (* (- x48 0) (- x48 0) eps eps 49) (* 2 4))))
                                    )
                                )

                                (integral (- k) k
                                    (lambda (x49 Real)
                                        (exp (- (/ (* (- x49 0) (- x49 0) eps eps 50) (* 2 4))))
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