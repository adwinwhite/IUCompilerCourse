(let ([x (let ([y (read)])
          (if (> y 0)
            (> y 2)
            (< y -2)))])
  (if (not x)
    42
    0))
