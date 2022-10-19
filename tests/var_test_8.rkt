(let ([x (let ([y 2]) (let ([x 4]) (+ x y)))])
	(let ([y (let ([x 30]) (+ x x))]) (- y x)))
