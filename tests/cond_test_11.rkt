(if (not (let ([x (and 
                    (not #f) 
                    (> (+ 34 56) (- 20)))])
           (or x (< 2 1))))
  42
  0)
