(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun eps () Real)
(assert (= eps 1.00))

(declare-fun k () Real)
(assert (= k 1))


(declare-fun d1 () Real)
(assert (>= d1 0))
(assert (<= d1 1))

(declare-fun d2 () Real)
(assert (>= d2 0))
(assert (<= d2 1))

(declare-fun d3 () Real)
(assert (>= d3 0))
(assert (<= d3 1))

(declare-fun d4 () Real)
(assert (>= d4 0))
(assert (<= d4 1))

(declare-fun d5 () Real)
(assert (>= d5 0))
(assert (<= d5 1))

(declare-fun d6 () Real)
(assert (>= d6 0))
(assert (<= d6 1))

(declare-fun d7 () Real)
(assert (>= d7 0))
(assert (<= d7 1))

(declare-fun d8 () Real)
(assert (>= d8 0))
(assert (<= d8 1))

(declare-fun d9 () Real)
(assert (>= d9 0))
(assert (<= d9 1))

(declare-fun d10 () Real)
(assert (>= d10 0))
(assert (<= d10 1))

(declare-fun d11 () Real)
(assert (>= d11 0))
(assert (<= d11 1))

(declare-fun d12 () Real)
(assert (>= d12 0))
(assert (<= d12 1))

(declare-fun d13 () Real)
(assert (>= d13 0))
(assert (<= d13 1))

(declare-fun d14 () Real)
(assert (>= d14 0))
(assert (<= d14 1))

(declare-fun d15 () Real)
(assert (>= d15 0))
(assert (<= d15 1))

(declare-fun d16 () Real)
(assert (>= d16 0))
(assert (<= d16 1))

(declare-fun d17 () Real)
(assert (>= d17 0))
(assert (<= d17 1))

(declare-fun d18 () Real)
(assert (>= d18 0))
(assert (<= d18 1))

(declare-fun d19 () Real)
(assert (>= d19 0))
(assert (<= d19 1))

(declare-fun d20 () Real)
(assert (>= d20 0))
(assert (<= d20 1))

(declare-fun d21 () Real)
(assert (>= d21 0))
(assert (<= d21 1))

(declare-fun d22 () Real)
(assert (>= d22 0))
(assert (<= d22 1))

(declare-fun d23 () Real)
(assert (>= d23 0))
(assert (<= d23 1))

(declare-fun d24 () Real)
(assert (>= d24 0))
(assert (<= d24 1))

(declare-fun d25 () Real)
(assert (>= d25 0))
(assert (<= d25 1))

(declare-fun d26 () Real)
(assert (>= d26 0))
(assert (<= d26 1))

(declare-fun d27 () Real)
(assert (>= d27 0))
(assert (<= d27 1))


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
                        
                                (integral (- k) d1
                                    (lambda (x1 Real)
                                        (exp (- (/ (* (- x1 0) (- x1 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d2
                                    (lambda (x2 Real)
                                        (exp (- (/ (* (- x2 0) (- x2 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d3
                                    (lambda (x3 Real)
                                        (exp (- (/ (* (- x3 0) (- x3 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d4
                                    (lambda (x4 Real)
                                        (exp (- (/ (* (- x4 0) (- x4 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d5
                                    (lambda (x5 Real)
                                        (exp (- (/ (* (- x5 0) (- x5 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d6
                                    (lambda (x6 Real)
                                        (exp (- (/ (* (- x6 0) (- x6 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d7
                                    (lambda (x7 Real)
                                        (exp (- (/ (* (- x7 0) (- x7 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d8
                                    (lambda (x8 Real)
                                        (exp (- (/ (* (- x8 0) (- x8 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d9
                                    (lambda (x9 Real)
                                        (exp (- (/ (* (- x9 0) (- x9 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d10
                                    (lambda (x10 Real)
                                        (exp (- (/ (* (- x10 0) (- x10 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d11
                                    (lambda (x11 Real)
                                        (exp (- (/ (* (- x11 0) (- x11 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d12
                                    (lambda (x12 Real)
                                        (exp (- (/ (* (- x12 0) (- x12 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d13
                                    (lambda (x13 Real)
                                        (exp (- (/ (* (- x13 0) (- x13 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d14
                                    (lambda (x14 Real)
                                        (exp (- (/ (* (- x14 0) (- x14 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d15
                                    (lambda (x15 Real)
                                        (exp (- (/ (* (- x15 0) (- x15 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d16
                                    (lambda (x16 Real)
                                        (exp (- (/ (* (- x16 0) (- x16 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d17
                                    (lambda (x17 Real)
                                        (exp (- (/ (* (- x17 0) (- x17 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d18
                                    (lambda (x18 Real)
                                        (exp (- (/ (* (- x18 0) (- x18 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d19
                                    (lambda (x19 Real)
                                        (exp (- (/ (* (- x19 0) (- x19 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d20
                                    (lambda (x20 Real)
                                        (exp (- (/ (* (- x20 0) (- x20 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d21
                                    (lambda (x21 Real)
                                        (exp (- (/ (* (- x21 0) (- x21 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d22
                                    (lambda (x22 Real)
                                        (exp (- (/ (* (- x22 0) (- x22 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d23
                                    (lambda (x23 Real)
                                        (exp (- (/ (* (- x23 0) (- x23 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d24
                                    (lambda (x24 Real)
                                        (exp (- (/ (* (- x24 0) (- x24 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d25
                                    (lambda (x25 Real)
                                        (exp (- (/ (* (- x25 0) (- x25 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d26
                                    (lambda (x26 Real)
                                        (exp (- (/ (* (- x26 0) (- x26 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- k) d27
                                    (lambda (x27 Real)
                                        (exp (- (/ (* (- x27 0) (- x27 0) eps eps) (* 2 4))))
                                    )
                                )

                    )
                )
            )
            (/ 1 4)
        )
    )
)

(check-sat) ; should be unsat
(exit)