Print[Resolve[Exists[{mu,sigma},
mu >= 20 && mu <= 30 && sigma >= 5 && sigma <= 15,
  !((Integrate[
       (1 / (sigma * Sqrt[2 * Pi]))
       * Exp[-(1/2) * ((x - mu) / sigma)^2],
       {x, 20 -(4 * 15), 5 - 5}
     ]
     + Integrate[
	   (1 / (5 * Sqrt[2 * Pi]))
	   * Exp[-(1/2) * ((z - 10) / 5)^2]
	   * (1 / (sigma * Sqrt[2 * Pi]))
	   * Exp[-(1/2) * ((x - mu) / sigma)^2],
	   {x, 5 - 5, 4 * 15},
	   {z, x/5, 4 * 15 + 30}
       ])
     >=
     ((1 - 0.1)
      * (Integrate[
       (1 / (sigma * Sqrt[2 * Pi]))
       * Exp[-(1/2) * ((x - mu) / sigma)^2],
       {x, 20 -(4 * 15), 5}
     ]
     + Integrate[
	   (1 / (5 * Sqrt[2 * Pi]))
	   * Exp[-(1/2) * ((z - 10) / 5)^2]
	   * (1 / (sigma * Sqrt[2 * Pi]))
	   * Exp[-(1/2) * ((x - mu) / sigma)^2],
	   {x, 5, 4 * 15 + 30},
	   {z, (x - 5)/5, 4 * 15 + 30}
       ])
     + (14/100000)))]]]