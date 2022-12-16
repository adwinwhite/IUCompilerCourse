(define (inc [x : Integer]) : Integer
  (+ x 1))

(define (dec [x : Integer]) : Integer
  (- x 1))

(let ([x (read)])
  (let ([op inc])
    (begin
      (if (eq? x 41)
        (set! op inc)
        (set! op dec))
      (op x))))
