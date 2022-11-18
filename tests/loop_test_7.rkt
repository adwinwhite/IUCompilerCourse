(let ([x 1])
  (begin
    (begin
        (set! x (+ x 2))
        (set! x (+ x x)))
    (+ x 36)))
