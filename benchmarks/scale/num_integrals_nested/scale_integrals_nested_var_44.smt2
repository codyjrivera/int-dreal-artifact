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
                    (integral (- k) k
                        (lambda (z Real)
                            (* 
                                (integral (- 1 k) z
                                    (lambda (y Real)
                                        (exp (- (/ (* (- y 1) (- y 1) eps eps) (* 2 4))))
                                    )
                                )
                                
                                (integral (- 0 k) z
                                    (lambda (x1 Real)
                                        (exp (- (/ (* (- x1 0) (- x1 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x2 Real)
                                        (exp (- (/ (* (- x2 0) (- x2 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x3 Real)
                                        (exp (- (/ (* (- x3 0) (- x3 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x4 Real)
                                        (exp (- (/ (* (- x4 0) (- x4 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x5 Real)
                                        (exp (- (/ (* (- x5 0) (- x5 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x6 Real)
                                        (exp (- (/ (* (- x6 0) (- x6 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x7 Real)
                                        (exp (- (/ (* (- x7 0) (- x7 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x8 Real)
                                        (exp (- (/ (* (- x8 0) (- x8 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x9 Real)
                                        (exp (- (/ (* (- x9 0) (- x9 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x10 Real)
                                        (exp (- (/ (* (- x10 0) (- x10 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x11 Real)
                                        (exp (- (/ (* (- x11 0) (- x11 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x12 Real)
                                        (exp (- (/ (* (- x12 0) (- x12 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x13 Real)
                                        (exp (- (/ (* (- x13 0) (- x13 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x14 Real)
                                        (exp (- (/ (* (- x14 0) (- x14 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x15 Real)
                                        (exp (- (/ (* (- x15 0) (- x15 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x16 Real)
                                        (exp (- (/ (* (- x16 0) (- x16 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x17 Real)
                                        (exp (- (/ (* (- x17 0) (- x17 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x18 Real)
                                        (exp (- (/ (* (- x18 0) (- x18 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x19 Real)
                                        (exp (- (/ (* (- x19 0) (- x19 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x20 Real)
                                        (exp (- (/ (* (- x20 0) (- x20 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x21 Real)
                                        (exp (- (/ (* (- x21 0) (- x21 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x22 Real)
                                        (exp (- (/ (* (- x22 0) (- x22 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x23 Real)
                                        (exp (- (/ (* (- x23 0) (- x23 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x24 Real)
                                        (exp (- (/ (* (- x24 0) (- x24 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x25 Real)
                                        (exp (- (/ (* (- x25 0) (- x25 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x26 Real)
                                        (exp (- (/ (* (- x26 0) (- x26 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x27 Real)
                                        (exp (- (/ (* (- x27 0) (- x27 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x28 Real)
                                        (exp (- (/ (* (- x28 0) (- x28 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x29 Real)
                                        (exp (- (/ (* (- x29 0) (- x29 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x30 Real)
                                        (exp (- (/ (* (- x30 0) (- x30 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x31 Real)
                                        (exp (- (/ (* (- x31 0) (- x31 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x32 Real)
                                        (exp (- (/ (* (- x32 0) (- x32 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x33 Real)
                                        (exp (- (/ (* (- x33 0) (- x33 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x34 Real)
                                        (exp (- (/ (* (- x34 0) (- x34 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x35 Real)
                                        (exp (- (/ (* (- x35 0) (- x35 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x36 Real)
                                        (exp (- (/ (* (- x36 0) (- x36 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x37 Real)
                                        (exp (- (/ (* (- x37 0) (- x37 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x38 Real)
                                        (exp (- (/ (* (- x38 0) (- x38 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x39 Real)
                                        (exp (- (/ (* (- x39 0) (- x39 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x40 Real)
                                        (exp (- (/ (* (- x40 0) (- x40 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x41 Real)
                                        (exp (- (/ (* (- x41 0) (- x41 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x42 Real)
                                        (exp (- (/ (* (- x42 0) (- x42 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x43 Real)
                                        (exp (- (/ (* (- x43 0) (- x43 0) eps eps) (* 2 4))))
                                    )
                                )

                                (exp (- (/ (* z z eps eps) (* 2 4))))
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
