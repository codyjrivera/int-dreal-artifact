Print[
    FindInstance[
        a >= 1 && a <= 2 &&
        ForAll[
            eps,
            eps > 1/10 && eps < 9/10,
            (
                Integrate[
                  Integrate[ 
                    Sin[(Pi / 2) * x] + a * eps * y, 
                    {x, 0,y}], 
                {y, 0, 1}]
                - Integrate[
                  Integrate[ 
                    Sin[(Pi / 2) * x] + a * eps * y, 
                    {x, 1, y}], 
                {y, 0, 1}]
                - (1/100)
                - (1/1000)
            )
            >
            0
        ],
        {a}
    ]
]
