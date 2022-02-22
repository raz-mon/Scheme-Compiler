(define a (make-vector 5 2))
(define (foo i)
          (* (vector-ref a i) i ...
          
(apply + `(,(foo 0) ,(foo 1) ,(foo 2) ,(foo 3) ,(foo 4)))
