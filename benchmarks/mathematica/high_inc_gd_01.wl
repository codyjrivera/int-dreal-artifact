Print[Resolve[Exists[ {mu, sigma},
mu > 548.4105 && mu < 588.4105 && sigma > 24248345.5428 && sigma < 24248385.5428,

  !(((2.02389 * (3307 * (2 / Sqrt[Pi]) *
  Integrate[ Exp[-1 * t^2] , {t, 0, (14147 - 2*mu)/(2 * Sqrt[2] * Sqrt[sigma])}]
    + 16693
  )) / (6693 * ((2/Sqrt[Pi]) *
      Integrate[ Exp[-1 * t^2] ,
      {t, 0, (12625081 - 2000*mu)/(400 * Sqrt[50 * sigma + 2253955380])}]
    ) + 13307))
  > (1 - 0.15))
  ], Reals]]
