;; Algorithmic Fairness: High Income vs. Gender: Univ. over model.
(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun eps () Real)
(assert (= eps 0.15))

(declare-fun mu () Real)
(assert (>= mu 548.4105))
(assert (<= mu 588.4105))

(declare-fun sigma () Real)
(assert (>= sigma 24248345.5428))
(assert (<= sigma 24248385.5428))

(assert
  (>
   (/
    (* 2.02389
       (+ (* 
           3307
	   (* (/ 2 (sqrt pi))
              (integral
               0
               (/ (- 14147 (* 2 mu))
                  (* 2 (sqrt 2) (sqrt sigma)))
               (lambda (t Real)
                 (exp (- (* t t)))))))
          16693))
    (+ (*
        6693
        (* (/ 2 (sqrt pi))
           (integral
            0
            (/ (- 12625081 (* 2000 mu))
               (* 400 (sqrt (+ (* 50 sigma) 2253955380))))
            (lambda (t Real)
              (exp (- (* t t)))))))
       (* 13307 4)))    
   (- 1 eps)))

(check-sat) ; should be unsat
(exit)

