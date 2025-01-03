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
                    (+ 
                        (integral (- k) k
                            (lambda (y Real)
                                (exp (- (/ (* (- y 1) (- y 1)) (* eps eps 2 4))))
                            )
                        )
                        {var_block}
                    )
                )
                
            )
            (/ 1 100)
        )
    )
)

(check-sat) ; should be unsat
(exit)'''

var_template = '''
                                (integral (- k) k
                                    (lambda ({var} Real)
                                        (exp (- (/ (* (- {var} 0) (- {var} 0) eps eps {factor}) (* 2 4))))
                                    )
                                )
'''


def save_string_to_file(file_path, content):
    try:
        with open(file_path, 'w') as file:
            file.write(content)
        print(f"File '{file_path}' saved successfully.")
    except Exception as e:
        print(f"An error occurred: {e}")


new_examples = './'
example_name = 'scale_integrals'
eps_lower = 0.5
eps_upper = 0.6
k = 1


def build_example(var_count):
    var_block = ''
    for i in range(1, var_count):
        var_block += var_template.format(var='x' + str(i), factor=str(i + 1))

    ex = template_dreal.format(eps_lower=eps_lower, eps_upper=eps_upper, k=k, var_block=var_block)

    return ex


for var_count in range(1, 100):
    save_string_to_file('{folder}/{file}_var_{var_count}.smt2'.format(
        folder=new_examples,
        file=example_name,
        var_count=var_count), build_example(var_count))