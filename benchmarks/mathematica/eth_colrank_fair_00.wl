eps=0.1
mu=25
sigma=10
maxsigma=10
t=5

Print[Resolve[
  !((NIntegrate[
       (1 / (sigma * Sqrt[2 * Pi]))
       * Exp[-(1/2) * ((x - mu) / sigma)^2],
       {x, 25-(4 * maxsigma), t - 5}
     ]
     + NIntegrate[
	   (1 / (5 * Sqrt[2 * Pi]))
	   * Exp[-(1/2) * ((z - 10) / 5)^2]
	   * (1 / (sigma * Sqrt[2 * Pi]))
	   * Exp[-(1/2) * ((x - mu) / sigma)^2],
	   {x, t - 5, 4 * maxsigma + 25},
	   {z, x/5, 4 * maxsigma + 25}
       ])
     >=
     ((1 - eps)
      * (NIntegrate[
       (1 / (sigma * Sqrt[2 * Pi]))
       * Exp[-(1/2) * ((x - mu) / sigma)^2],
       {x, 25-(4 * maxsigma), t}
     ]
     + NIntegrate[
	   (1 / (5 * Sqrt[2 * Pi]))
	   * Exp[-(1/2) * ((z - 10) / 5)^2]
	   * (1 / (sigma * Sqrt[2 * Pi]))
	   * Exp[-(1/2) * ((x - mu) / sigma)^2],
	   {x, t, 4 * maxsigma + 25},
	   {z, (x - 5)/5, 4 * maxsigma + 25}
       ])
     + (14/100000)))]]
