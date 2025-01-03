Print[Resolve[Exists[{eps, delta},
  eps > 0.1 && eps <= 1 && delta > 1/1000 &&
      delta <= 1, !(((Power[eps, 4] / Power[2,4]) *
      Power[Integrate[Exp[-eps * Abs[x]], {x, -(1 / eps) * Log[4 / delta], (1 / eps) *
          Log[4 / delta]}], 4])
      >
      (1 - delta))]]]
