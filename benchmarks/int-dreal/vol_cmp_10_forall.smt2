; Synthesis of f(x,y,eps)= pow(sin x,2) + exp (3 eps y).
(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun a () Real)
(assert (>= a 1))
(assert (<= a 2))

(declare-fun delta () Real)
(assert (= delta 0.001))

(assert 
 (forall ((eps Real)) 
    (=> 
      (and (> eps 0.1) (< eps 0.9))
      (>=
        (+  (integral 0 1
                  (lambda (y Real)
                  (integral 0 y
                            (lambda (x Real)
                            (+ (* 
                                  (sin (* (/ pi 2) x)) 
                                  (sin (* (/ pi 2) x))
                                )
                               (exp (* 3 a eps y)) 
                            )))))
            (- (integral 0 1
                  (lambda (y Real)
                  (integral 1 y
                            (lambda (x Real)
                            (+ (* 
                                  (sin (* (/ pi 2) x)) 
                                  (sin (* (/ pi 2) x))
                                )
                               (exp (* 3 a eps y))
                            ))))))
            (- (/ 1 100))
            (- delta)
        )  
            
        0
      )
)))

(check-sat)
(exit)