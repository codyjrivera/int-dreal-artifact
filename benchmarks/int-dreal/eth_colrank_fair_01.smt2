;; FairSquare Hiring
(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun eps () Real)
(assert (= eps 0.1))

(declare-fun mu () Real)
(assert (>= mu 20))
(assert (<= mu 30))

(declare-fun sigma () Real)
(assert (>= sigma 10))
(assert (<= sigma 15))

(declare-fun max-sigma () Real)
(assert (= max-sigma 15))

(declare-fun t () Real)
(assert (= t 5))

(assert
 (not
  (>=
   (+
    (integral
     (- 20 (* 4 max-sigma)) ; -infty
     (- t 5)
     (lambda (x Real)
       (*
	(/ 1 (* sigma (sqrt (* 2 pi))))
	(exp
	 (* (- (/ 1 2))
	    (* (/ (- x mu) sigma)
	       (/ (- x mu) sigma)))))))
    (integral
     (- t 5)
     (+ 30 (* 4 max-sigma)) ; infty
     (lambda (x Real)
       (integral
	(/ x 5)
	(+ 30 (* 4 max-sigma)) ; infty
	(lambda (z Real)
	  (*
	   (/ 1 (* 5 (sqrt (* 2 pi))))
	   (exp
	    (* (- (/ 1 2))
	       (* (/ (- z 10) 5)
		  (/ (- z 10) 5))))
	   (/ 1 (* sigma (sqrt (* 2 pi))))
	   (exp
	    (* (- (/ 1 2))
	       (* (/ (- x mu) sigma)
		  (/ (- x mu) sigma))))))))))
   (*
    (- 1 eps)
    (+
     (integral
      (- 20 (* 4 max-sigma)) ; -infty
      t
      (lambda (x Real)
	(*
	 (/ 1 (* sigma (sqrt (* 2 pi))))
	 (exp
	  (* (- (/ 1 2))
	     (* (/ (- x mu) sigma)
		(/ (- x mu) sigma)))))))
     (integral
      t
      (+ 30 (* 4 max-sigma)) ; infty
      (lambda (x Real)
	(integral
	 (/ (- x 5) 5)
         (+ 30 (* 4 max-sigma)) ; infty
	 (lambda (z Real)
	   (*
	    (/ 1 (* 5 (sqrt (* 2 pi))))
	    (exp
	     (* (- (/ 1 2))
		(* (/ (- z 10) 5)
		   (/ (- z 10) 5))))
	    (/ 1 (* sigma (sqrt (* 2 pi))))
	    (exp
	     (* (- (/ 1 2))
		(* (/ (- x mu) sigma)
		   (/ (- x mu) sigma)))))))))
     (/ 14 100000))))))

(check-sat) ; should be unsat
(exit)

