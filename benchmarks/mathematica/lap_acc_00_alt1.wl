Print[Resolve[Exists[{eps, delta},
  eps > 1/10 && eps <= 1 && delta > 1/1000 &&
      delta <= 1, !((((eps * eps) / 4) *
      Integrate[Exp[-eps * Abs[x]], {x, -(1 / eps) * Log[2 / delta], (1 / eps) *
          Log[2 / delta]}] * Integrate[
         Exp[-eps * Abs[y]], {y, -(1 / eps) * Log[2 / delta], (1 / eps) *
                Log[2 / delta]}])
      >
      (1 - delta))], Reals]]
