Print[Resolve[Exists[{eps, delta},
  eps > 1/10 && eps <= 1 && delta > 1/1000 && delta <= 1,
  !((((Power[eps, 3] / Power[2,3]) *
      Power[Integrate[Exp[-eps * Abs[x]], {x, -(1 / eps) * Log[3 / delta], (1 / eps) *
          Log[3 / delta]}], 3]))
      >
      (1 - delta))], Reals]]
