((lambda (a b c d e f)
	(a b c d e f))
	(lambda (a b c d e) (cons a (cons b (cons c (cons d e)))))
	((lambda (a) (* a a)) ((lambda (b) b) 1))
	((lambda (a) ((lambda (b) b) 1)) 1)
	((lambda (a) (+ a 0)) ((lambda (b) 1) 0))
	((lambda (a) 1) ((lambda (b) 0) 2))
	((lambda (a) a) ((lambda (b) b) 1)))
