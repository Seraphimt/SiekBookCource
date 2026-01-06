(let ([a (let ([b (let ([d 10]) (let ([f 12]) (+ d f))) ]) (+ b 1))])
    (let ([c 10])
	  (+ a c)))