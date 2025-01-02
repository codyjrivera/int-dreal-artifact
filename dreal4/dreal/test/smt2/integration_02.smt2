;; Gaussian, from differential privacy
(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun eps () Real)
(assert (>= eps 0.01))
(assert (<= eps 1))

(declare-fun k () Real)
(assert (= k 200))

(declare-fun u0 () Real)
(assert (= u0 1))

(declare-fun v0 () Real)
(assert (= v0 0))

(declare-fun u1 () Real)
(assert (= u1 0))

(declare-fun v1 () Real)
(assert (= v1 1))

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
            (integral (- v0 k) z 
            (lambda (y Real)
            (integral (- u0 k) z
            (lambda (x Real)
                (*  (exp (- (/ (* (- x u0) (- x u0))
                               (* 2 (/ 4 (* eps eps))))))
                    (exp (- (/ (* (- y v0) (- y v0))
                               (* 2 (/ 4 (* eps eps))))))
                    (exp (- (/ (* z z)
                               (* 2 (/ 4 (* eps eps))))))
                    ))))))))
        (/ 3 100))
        (+ 
        (* 
            (exp eps)
            (/ 
                1
                (* 
                    2 
                    pi 
                    (pow (sqrt (/ 4 (* eps eps))) 3)
                    (sqrt (* 2 pi))))
            (integral (- k) k
            (lambda (z Real)
            (integral (- v1 k) z 
            (lambda (y Real)
            (integral (- u1 k) z
            (lambda (x Real)
                (*  (exp (- (/ (* (- x u1) (- x u1))
                               (* 2 (/ 4 (* eps eps))))))
                    (exp (- (/ (* (- y v1) (- y v1))
                               (* 2 (/ 4 (* eps eps))))))
                    (exp (- (/ (* z z)
                               (* 2 (/ 4 (* eps eps))))))
                    ))))))))
        (/ 1 8))
    )))

(check-sat) ; should be unsat
(exit)

