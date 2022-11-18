(let ([x 10])
  (+ x (begin
         (let ([y 12])
           (begin
             (set! x 20)
             (set! x (+ y x))))
         x)))
