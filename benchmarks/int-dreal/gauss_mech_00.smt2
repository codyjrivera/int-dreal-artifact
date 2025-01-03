;; Gaussian mechanism
(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun eps () Real)
(assert (> eps 0.1))
(assert (< eps 1))

(declare-fun width () Real)
(assert (= width 10))

(declare-fun a () Real)
(assert (= a (- width)))

(declare-fun b () Real)
(assert (= b width))

(declare-fun c () Real)
(assert (= c (- width)))

(declare-fun d () Real)
(assert (= d width))

(declare-fun u0 () Real)
(assert (= u0 0))

(declare-fun v0 () Real)
(assert (= v0 0))

(declare-fun u1 () Real)
(assert (= u1 1))

(declare-fun v1 () Real)
(assert (= v1 0))

(assert
   (not
    (<=
        (* (/ 
                (* 1 eps eps)
                (* 2 pi 2.2 2.2))
            (integral a b 
            (lambda (x Real)
            (integral c d
            (lambda (y Real)
                (*  (exp (- (/ (* (- x u0) (- x u0) eps eps)
                               (* 2 2.2 2.2))))
                    (exp (- (/ (* (- y v0) (- y v0) eps eps)
                               (* 2 2.2 2.2))))
                    ))))))
        (+ 
        (* 
            (exp eps)
            (/ 
                (* 1 eps eps)
                (* 2 pi 2.2 2.2))
            (integral a b 
            (lambda (x Real)
            (integral c d
            (lambda (y Real)
                (*  (exp (- (/ (* (- x u1) (- x u1) eps eps)
                               (* 2 2.2 2.2))))
                    (exp (- (/ (* (- y v1) (- y v1) eps eps)
                               (* 2 2.2 2.2))))
                    ))))))
        (/ 1 8)
        )
    )))

(check-sat) ; should be unsat
(exit)

