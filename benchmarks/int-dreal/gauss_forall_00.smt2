; Synthesis of constants for gaussian mechanism.
(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun a () Real)
(assert (>= a 0.25))
(assert (<= a 0.75))

(declare-fun k () Real)
(assert (= k 20))

(declare-fun delta () Real)
(assert (= delta 0.001))

(assert 
 (forall ((eps Real)) 
    (=> 
      (and (> eps 0.5) (< eps 0.9))
      (>
        (+
          (* 
            (/ (* a (- 1 a) eps eps)
              (* 2 pi))
            (integral 
              (- k)
              k
              (lambda (x Real)
                (integral
                  x
                  k
                  (lambda (y Real)
                    (*
                      (exp
                        (-
                          (/
                            (* a a eps eps x x)
                            2
                          )
                        )
                      )
                      (exp
                        (-
                          (/
                            (* (- 1 a) (- 1 a) eps eps (- y 1) (- y 1))
                            2
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
          (- 0.5)
          (- delta)
        )
        0
      )
    )))

(check-sat)
(exit)
