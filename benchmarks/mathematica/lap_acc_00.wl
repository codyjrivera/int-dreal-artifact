Print[Resolve[Exists[{eps, delta},
  eps > 0.1 && eps <= 1 && delta > 1/1000 &&
      delta <= 1, !((((eps * eps) / 4) *
      Integrate[Integrate[
        Exp[-eps * Abs[x]] * Exp[-eps * Abs[y]], {y, -(1 / eps) * Log[2 / delta], (1 / eps) *
                Log[2 / delta]}], {x, -(1 / eps) * Log[2 / delta], (1 / eps) *
          Log[2 / delta]}])
      >
      (1 - delta))]]]
