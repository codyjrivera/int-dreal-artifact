Print[Resolve[Exists[ {eps, x, y},eps > 0.1 && eps < 0.2,!((
  Integrate[Integrate[ Sin[(Pi / 2) * x] + eps * y, {x, 0,y} ], {y, 0, 1}]
 )
  > (Integrate[Integrate[ Sin[(Pi / 2) * x] + eps * y, {x, 0,y * y} ], {y, 0, 1}] + 1/100))
  ], Reals]]