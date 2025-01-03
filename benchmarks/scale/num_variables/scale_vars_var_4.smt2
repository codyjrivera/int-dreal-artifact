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

                    )
                )
            )
            (/ 1 4)
        )
    )
)

(check-sat) ; should be unsat
(exit)