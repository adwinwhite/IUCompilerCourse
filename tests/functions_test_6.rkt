(define (fib [n : Integer]) : Integer 
  (if (<= n 1)
    1
    (+ (fib (- n 1)) (fib (- n 2)))))

(let ([x 2])
  (let ([y 4])
    (+ (fib (+ x y)) (fib (+ y x)))))
