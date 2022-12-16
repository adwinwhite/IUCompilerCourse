(define (inc [x : Integer]) : Integer
  (+ x 1))

(define (dec [x : Integer]) : Integer
  (- x 1))

(define (choose-func [plus : Boolean]) : (Integer -> Integer)
  (if plus
    inc
    dec))

(let ([x (read)])
  (let ([op inc])
    (begin
      (set! op (choose-func #f))
      (op x))))
