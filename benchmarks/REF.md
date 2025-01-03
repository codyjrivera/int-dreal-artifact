# Quick Reference for ∫dReal
by Cody Rivera and Bishnu Bhusal, Version 1.0, 2025.

## ∫dReal options

∫dReal is normally executed using the following command-line:
```
dreal [options] input-file.smt2
```
where input-file.smt2 is an input file in the format that
I will briefly describe below, and `[options]` may include `--precision VAL`,
to set a value for delta which is not the default (0.001).

There are two options specific to ∫dReal, both passed in as
environment variables
* `ARB_PRECISION`: denotes the precision that arbitrary-precision
  arithmetic will be carried out to. We consistently use '32' as an 
  argument for this variable.
* `MAX_PRUNE_WIDTH`: denotes the maximum width at which pruning for integration
  will be tried. We consistently use '0.1' as an argument for this variable.

Therefore, to run the query `input-file.smt2` with a given Arb precision of
64 bits, we perform the following command:
```
ARB_PRECISION=64 dreal input-file.smt2
```

## ∫dReal input language

Below is an example of an input query in the input format expected:
```
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
                            (+ (sin (* (/ pi 2) x)) 
                               (* a eps y) 
                            )))))
            (- (integral 0 1
                  (lambda (y Real)
                  (integral 1 y
                            (lambda (x Real)
                            (+ (sin (* (/ pi 2) x)) 
                               (* a eps y) 
                            ))))))
            (- (/ 1 100))
            (- delta)
        )  
            
        0
      )
)))

(check-sat)
(exit)
```

We briefly discuss the interesting features of this query.
We declare existentially-quantified variables as follows:
```
(declare-fun a () Real)
(assert (>= a 1))
(assert (<= a 2))
```
The two asserts following the `declare-fun` set upper and lower bounds for
the interval `a`. Endpoints need not be inclusive, and can be strict if
`<=` is replaced by `<`. 

The statement
```
(forall ((eps Real))
    ;; body
)
```
denotes a logical forall. The variable `eps` occurs free in the body.

The statement
```
(integral l u
    (lambda (y Real)
    ;; body
    ))
```
denotes an integral expression. It denotes the integration from l
to u of a function specified in the body, with respect to the variable y.

