(define foo (lambda (x)
	(let ((x (+ x 1)))
		(lambda (y)
			(let ((y (+ y 1)))
				(lambda (z) 
					(+ x y z)))))))
					
(define f1 (foo 1))
(define f12 (f1 2))
(f12 3)
