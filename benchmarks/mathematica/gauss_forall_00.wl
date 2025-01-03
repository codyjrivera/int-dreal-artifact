Print[
    FindInstance[
        a >= 1/4 && a <= 3/4 &&
        ForAll[
            eps,
            eps > 5/10 && eps < 9/10,
            (
                ((a * (1 - a) * eps * eps)/(2 * Pi)) *
                Integrate[
                Integrate[
                    Exp[-(
                        (a * a * eps * eps * x * x) /
                        2
                    )] *
                    Exp[-(
                        ((1 - a) * (1 - a) * eps * eps * (y - 1) * (y - 1)) /
                        2
                    )],
                    {y, x, 20}
                ], 
                    {x, -20, 20}
                ]
            ) - (5/10) - (1/1000)
            >
            0
        ],
        {a}
    ]
]
