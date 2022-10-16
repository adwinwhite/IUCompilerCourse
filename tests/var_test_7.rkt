(let ([x (let ([y 10]) (let ([x 30]) (+ x y)))])
	(let ([y 20]) (+ x y)))
