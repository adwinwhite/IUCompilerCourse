(let ([x (vector 0)])
  (begin
    (let ([y (vector 1 (vector 42))])
      (set! x (vector-ref y 1)))
    (vector-ref x 0)))
