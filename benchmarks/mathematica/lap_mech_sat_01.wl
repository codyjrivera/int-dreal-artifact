Print[Resolve[
    Exists[eps, eps > 1/10 && eps < 1 ,!((Integrate[Exp[-eps * Abs[x]], {x, 1, 2}]) <= (Exp[eps / 2] *
        Integrate[Exp[-eps * Abs[x + 1]], {x, 1, 2}]))]]]