(define foo
	(lambda (n e)
		(if (= n (* 2 (/ n 2)))
			(foo (/ n 2) (+ e 1))
			e)))

(apply foo '(64 0))
