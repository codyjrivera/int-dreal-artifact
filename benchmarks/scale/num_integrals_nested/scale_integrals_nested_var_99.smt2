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

                                (integral (- 0 k) z
                                    (lambda (x44 Real)
                                        (exp (- (/ (* (- x44 0) (- x44 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x45 Real)
                                        (exp (- (/ (* (- x45 0) (- x45 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x46 Real)
                                        (exp (- (/ (* (- x46 0) (- x46 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x47 Real)
                                        (exp (- (/ (* (- x47 0) (- x47 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x48 Real)
                                        (exp (- (/ (* (- x48 0) (- x48 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x49 Real)
                                        (exp (- (/ (* (- x49 0) (- x49 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x50 Real)
                                        (exp (- (/ (* (- x50 0) (- x50 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x51 Real)
                                        (exp (- (/ (* (- x51 0) (- x51 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x52 Real)
                                        (exp (- (/ (* (- x52 0) (- x52 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x53 Real)
                                        (exp (- (/ (* (- x53 0) (- x53 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x54 Real)
                                        (exp (- (/ (* (- x54 0) (- x54 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x55 Real)
                                        (exp (- (/ (* (- x55 0) (- x55 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x56 Real)
                                        (exp (- (/ (* (- x56 0) (- x56 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x57 Real)
                                        (exp (- (/ (* (- x57 0) (- x57 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x58 Real)
                                        (exp (- (/ (* (- x58 0) (- x58 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x59 Real)
                                        (exp (- (/ (* (- x59 0) (- x59 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x60 Real)
                                        (exp (- (/ (* (- x60 0) (- x60 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x61 Real)
                                        (exp (- (/ (* (- x61 0) (- x61 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x62 Real)
                                        (exp (- (/ (* (- x62 0) (- x62 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x63 Real)
                                        (exp (- (/ (* (- x63 0) (- x63 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x64 Real)
                                        (exp (- (/ (* (- x64 0) (- x64 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x65 Real)
                                        (exp (- (/ (* (- x65 0) (- x65 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x66 Real)
                                        (exp (- (/ (* (- x66 0) (- x66 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x67 Real)
                                        (exp (- (/ (* (- x67 0) (- x67 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x68 Real)
                                        (exp (- (/ (* (- x68 0) (- x68 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x69 Real)
                                        (exp (- (/ (* (- x69 0) (- x69 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x70 Real)
                                        (exp (- (/ (* (- x70 0) (- x70 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x71 Real)
                                        (exp (- (/ (* (- x71 0) (- x71 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x72 Real)
                                        (exp (- (/ (* (- x72 0) (- x72 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x73 Real)
                                        (exp (- (/ (* (- x73 0) (- x73 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x74 Real)
                                        (exp (- (/ (* (- x74 0) (- x74 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x75 Real)
                                        (exp (- (/ (* (- x75 0) (- x75 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x76 Real)
                                        (exp (- (/ (* (- x76 0) (- x76 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x77 Real)
                                        (exp (- (/ (* (- x77 0) (- x77 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x78 Real)
                                        (exp (- (/ (* (- x78 0) (- x78 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x79 Real)
                                        (exp (- (/ (* (- x79 0) (- x79 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x80 Real)
                                        (exp (- (/ (* (- x80 0) (- x80 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x81 Real)
                                        (exp (- (/ (* (- x81 0) (- x81 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x82 Real)
                                        (exp (- (/ (* (- x82 0) (- x82 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x83 Real)
                                        (exp (- (/ (* (- x83 0) (- x83 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x84 Real)
                                        (exp (- (/ (* (- x84 0) (- x84 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x85 Real)
                                        (exp (- (/ (* (- x85 0) (- x85 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x86 Real)
                                        (exp (- (/ (* (- x86 0) (- x86 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x87 Real)
                                        (exp (- (/ (* (- x87 0) (- x87 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x88 Real)
                                        (exp (- (/ (* (- x88 0) (- x88 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x89 Real)
                                        (exp (- (/ (* (- x89 0) (- x89 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x90 Real)
                                        (exp (- (/ (* (- x90 0) (- x90 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x91 Real)
                                        (exp (- (/ (* (- x91 0) (- x91 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x92 Real)
                                        (exp (- (/ (* (- x92 0) (- x92 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x93 Real)
                                        (exp (- (/ (* (- x93 0) (- x93 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x94 Real)
                                        (exp (- (/ (* (- x94 0) (- x94 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x95 Real)
                                        (exp (- (/ (* (- x95 0) (- x95 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x96 Real)
                                        (exp (- (/ (* (- x96 0) (- x96 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x97 Real)
                                        (exp (- (/ (* (- x97 0) (- x97 0) eps eps) (* 2 4))))
                                    )
                                )

                                (integral (- 0 k) z
                                    (lambda (x98 Real)
                                        (exp (- (/ (* (- x98 0) (- x98 0) eps eps) (* 2 4))))
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
