(define sfx
    (lambda (bool)
      (if bool 
          (lambda (v s i)
            (vector-set! v i (string-ref s i))
            v)
          (lambda (v s i)
            (string-set! s i (vector-ref v i))
            s))))

(let ((vec (make-vector 5 #\a))
		(str (make-string 5 #\b)))
	(cons ((sfx #t) vec str 3) ((sfx #f) vec str 2)))
