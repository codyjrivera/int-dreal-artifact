template_dreal = '''(set-logic QF_NRA)

(declare-fun pi () Real)
(assert (>= pi 3.141592653589793238461))
(assert (<= pi 3.141592653589793238463))

(declare-fun eps () Real)
(assert (>= eps {eps_lower:.2f}))
(assert (<= eps {eps_upper:.2f}))

(declare-fun k () Real)
(assert (= k {k}))

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
            (* (integral (- 1 k) z
            (lambda (y Real)
                (exp (- (/ (* (- y 1) (- y 1) eps eps)
                               (* 2 4))))))

            (integral (- 0 k) z
            (lambda (x Real)
                (exp (- (/ (* (- x 0) (- x 0) eps eps)
                               (* 2 4))))

                    ))

                    (exp (- (/ (* z z eps eps)
                               (* 2 4))))

                    )

                    ))
            )
        (/ 3 100)
        )
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
            (* (integral (- 0 k) z
            (lambda (y Real)
                (exp (- (/ (* (- y 0) (- y 0) eps eps)
                               (* 2 4))))))

            (integral (- 1 k) z
            (lambda (x Real)
                  (exp (- (/ (* (- x 1) (- x 1) eps eps)
                               (* 2 4))))

                    ))

                    (exp (- (/ (* z z eps eps)
                               (* 2 4))))

                    )

                    ))
            )
        (/ 1 8)
        )
    )))

(check-sat) ; should be unsat
(exit)
'''

def save_string_to_file(file_path, content):
    try:
        with open(file_path, 'w') as file:
            file.write(content)
        print(f"File '{file_path}' saved successfully.")
    except Exception as e:
        print(f"An error occurred: {e}")


new_examples = './'
example_name = 'svt_product'
eps_lower = 0.1
for k in range(4, 48 + 1, 4):
    for eps in range(1, 5):
        eps_upper = eps_lower + 2 * eps * eps_lower
        ex = template_dreal.format(eps_lower=eps_lower, eps_upper=eps_upper, k=k)
        save_string_to_file('{folder}/{file}_eps_{lower:.2f}_{upper:.2f}_k_{k}.smt2'.format(
            folder=new_examples,
            file=example_name,
            lower=eps_lower,
            upper=eps_upper,
            k=k), ex)
