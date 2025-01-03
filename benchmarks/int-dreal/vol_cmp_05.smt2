; f(x,y,eps) = sin x + sin (eps y)
(set-logic QF_NRA)


(declare-fun eps () Real)
(assert (>= eps 0.1))
(assert (<= eps 0.2))

(declare-fun pi () Real)
(assert (= pi 3.14159265358979323846264338327950288419716939937510))



(assert 
 (not
    (<  (integral 0 1
                  (lambda (y Real)
                  (integral 0 y
                            (lambda (x Real)
                            (+ (sin (* (/ pi 2) x))
                               (sin (* (/ pi 2) eps y)) 
                            )))))
        (+ (integral 0 1
                  (lambda (y Real)
                  (integral 0 (* y y)
                            (lambda (x Real)
                            (+ (sin (* (/ pi 2) x))
                               (sin (* (/ pi 2) eps y)) 
                            )))))
          (/ 1 100)
        )
    )
 )
)

(check-sat)
(exit)