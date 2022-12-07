(let ([i 0])
  (let ([x (vector 0)])
    (begin
      (while (< i 65535)
        (begin
          (set! x (vector i))
          (set! i (+ i 1))))
      42)))
