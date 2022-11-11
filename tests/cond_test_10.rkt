(let ([x (not (>= 3 2))])
  (if (or x (eq? x #f))
    42 
    0))
