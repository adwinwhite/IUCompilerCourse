 (define (sum [x1 : Integer] [x2 : Integer] [x3 : Integer] [x4 : Integer] [x5 : Integer] [x6 : Integer] [x7 : Integer]) : Integer 
   (+ x1 (+ x2 (+ x3 (+ x4 (+ x5 (+ x6 x7)))))))

(sum 1 2 3 4 5 6 21)
