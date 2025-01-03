Print[Resolve[
    Exists[eps, eps > 0.1 && eps < 1 ,!((Integrate[Exp[-eps * Abs[x]], {x, 1, 2}]) <= (Exp[eps] *
        Integrate[Exp[-eps * Abs[x + 1]], {x, 1, 2}]))]]]