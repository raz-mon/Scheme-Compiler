";;;                Constants:"

";;;    ScmNil:"
'()

";;;    ScmBoolean:"
#t
#f


";;;    ScmChar:"
#\a
#\r

555
123.321

";;;    ScmString:"
'("raz" "almog")
"raz"
"almog"
; Can't add multipule line strings here, since the windows os adds '\r' to each line for some reason --> 
; Generate file in Linux and test from there or just test with scheme, it deletes these meta-chars.

;;; Constant pairs (ScmPair):
'(1 2 3 4)
'(a b c d)
'(a '(b c) '())

;;; Constant Vectors:
'#(1 2 3)
'#(a b c)
'#("raz" "almog" 1 2 123 1341324123.412343 g)
'#() ;          Doesn't work for some reason (something in code-gen.ml).

;;; Constant 


";;;                    Scmvar' - free, param and bound - get, set, getBox, setBox:"
;; VarFree:
(define g 5)
g

(define h (lambda (x y) y))

;; VarParam:
(define f (lambda (x) x))
 (f 512)
 (f 4.2)
 (f 'a)
 (f #t)
 (h f g)

;; VarBound:
 (define f (lambda (x) (lambda (y) x)))
  ((f 4) 5)                                 ; return 4
  ((f g) 1)                                 ; return g
  ((((f f) 1) #t)#f)                        ; need to return #t


";;;                    ScmBox':"


";;;                    ScmBoxGet':"

";;;                    ScmBoxSet':"

";;;                    ScmIf':"
(if #t 1 2)                                             ; 1
(define test (if #t 3 4))                               ; 3
test
(define test (lambda (t dit dif) (if t dit dif)))       
(test #t 55 11)                                         ; 55
(test #f 55 11)                                         ; 11
(test (< 4 2) 55 11)                                    ; 11
(test ((((f f) 1) #t)#f) 55 11)                         ; 55

";;;                    ScmSeq':"

(define y 10)
y
(define test_seq (lambda (x) (set! y 5) 2 (test #t 55 11)  4 5 x))
(test_seq 10)
y

";;;                    ScmSet':"
(define a 'a)           ; a <- 'a
(define b 'b)           ; b <- 'b
a
b
(define c 'c)
(set! c a)
(set! a b)              ; a <- 'b
(set! b c)              ; b <- 'a
a                   
b
((lambda (x y z) (set! x y)) a c)
a                       ; a <- 'a
b                       ; b <- 'b

(define test_set (lambda (x y z) (set! x y)))
(test_set a b a)
a
b
;; Test1:
(define x 0)
(set! x 3)
(if #f 1 x)
(if #t (set! x 2) x)
x

;; Test2:

";;;                    ScmDef':"

";;;                    ScmOr':"

";;;                    ScmLambdaSimple':"
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) x) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) y) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) z) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) a) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) s) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) q) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) w) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) e) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)
(define f (lambda (x y z) (lambda (a s) (lambda (q w e r) r) ) ) )
(((f 1 2 3) 4 5) 6 7 8 9)


((lambda () 53))
(define f (lambda (x y z) y) )
(define g (lambda () (f 1 2 3) ) )
(g)


";;;                    ScmLambdaOpt':"
((lambda (x y . z) z) 1 2 3 4)

(define f1 (lambda x x))
(f1 5)
(define f2 (lambda (x . y) x))
(f2 1)
(f2 1 2)
(f2 1 2 3)
(f2 1 2 3 4)
(define f3 (lambda (x . y) y))
(f3 1)
(f3 1 2)
(f3 1 2 3)
(f3 1 2 3 4)

(define f1 (lambda (x y z w . t) x))
(define f2 (lambda (x y z w . t) y))
(define f3 (lambda (x y z w . t) z))
(define f4 (lambda (x y z w . t) w))
(define f5 (lambda (x y z w . t) t))
(f1 1 2 3 4 5 6 7 8)
(f2 1 2 3 4 5 6 7 8)
(f3 1 2 3 4 5 6 7 8)
(f4 1 2 3 4 5 6 7 8)
(f5 1 2 3 4 5 6 7 8)

(define f (lambda x (lambda y (lambda z x))))
(((f)))
(((f 1)))
(((f 1 2)))
(((f 1 2 3)))
(((f) 2 3 4))
(((f 1 2 3 4) 5 6))
(((f) 2) 3 4 5 6)
(define f (lambda x (lambda y (lambda z y))))
(((f)))
(((f 1)))
(((f 1 2)))
(((f 1 2 3)))
(((f) 2 3 4))
(((f 1 2 3 4) 5 6))
(((f) 2) 3 4 5 6)
(define f (lambda x (lambda y (lambda z z))))
(((f)))
(((f 1)))
(((f 1 2)))
(((f 1 2 3)))
(((f) 2 3 4))
(((f 1 2 3 4) 5 6))
(((f) 2) 3 4 5 6)

(define f (lambda (x . t) (lambda y (lambda z x))))
(((f 1)))
(((f 1)))
(((f 1 2)))
(((f 1 2 3)))
(((f 1) 2 3 4))
(((f 1 2 3 4) 5 6))
(((f 1) 2) 3 4 5 6)
(define f (lambda (x . t) (lambda y (lambda z t))))
(((f 1)))
(((f 1)))
(((f 1 2)))
(((f 1 2 3)))
(((f 1) 2 3 4))
(((f 1 2 3 4) 5 6))
(((f 1) 2) 3 4 5 6)
(define f (lambda (x . t) (lambda y (lambda z y))))
(((f 1)))
(((f 1)))
(((f 1 2)))
(((f 1 2 3)))
(((f 1) 2 3 4))
(((f 1 2 3 4) 5 6))
(((f 1) 2) 3 4 5 6)
(define f (lambda (x . t) (lambda y (lambda z z))))
(((f 1)))
(((f 1)))
(((f 1 2)))
(((f 1 2 3)))
(((f 1) 2 3 4))
(((f 1 2 3 4) 5 6))
(((f 1) 2) 3 4 5 6)



";;;                    ScmApplic':"

";;;                    ScmApplicTP':"
(define f (lambda (x) x))
(define g (lambda (x y z) (f y) ) )
(define h (lambda () (g 1 2 3) ) )
(h)

( (lambda (a s d f g) ((lambda (q w e r t) r ) 1 2 3 4 5) ) 6 7 8 9 10 )

( (lambda (a s d f g) ((lambda (q w e r t) ((lambda (b) 555) 999) ) 1 2 3 4 5) ) 6 7 8 9 10 )

";;;                    car, cdr, cons, car-set!, cdr-set!, apply:"


;;; apply:
(define f 
   (lambda (x) 
      333
      (apply (lambda (x) x) '(2))
      555
      (apply (lambda (x y z) x) '(1 2 3))
   ) 
)
(f 2)
(apply (lambda (x y) y) 1 '(2))
(apply f '(2))
(apply (lambda (x) x) '(2))

