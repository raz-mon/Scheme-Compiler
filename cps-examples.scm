;;; cps-examples.scm
;;; Examples of converting procedures from direct style, through
;;; CPS, arriving at the stack machine.
;;;
;;; Programmer: Mayer Goldberg, 2021

;;; This file contains several functions, each implemented
;;; differently in Scheme. To keep the code reasonably neat,
;;; each implementation is "buried" within a letrec. This is
;;; a bit different from what you saw in class, but it's neater.

;;; Each implementation is indexed by a number. Here is the key:
;;;   1 -- The function in direct style
;;;   2 -- The function in CPS
;;;   3 -- The function in CPS, with the representation
;;;        of the continuation abstracted away behind an
;;;        interface
;;;   4 -- The function in CPS, using records in place of closures
;;;   5 -- The function in CPS, using a flat structure rather than
;;;        nested records
;;;   6 -- The function in pseudo-assembly -- the stack machine

;;; Worked-out examples in order:
;;;    1. fact
;;;    2. fib
;;;    3. ack
;;;    4. length
;;;    5. replace-first
;;;    6. replace-all-flat
;;;    7. hanoi
;;;    8. fast-fib
;;;    9. power
;;;   10. sin
;;;   11. sum
;;;   12. perm

;;; Global helper procedures

(define with (lambda (s f) (apply f s)))

(define *stack* 'moshe)

(define push (lambda (x) (set! *stack* (cons x *stack*))))

(define pop
  (lambda ()
    (let ((x (car *stack*)))
      (set! *stack* (cdr *stack*))
      x)))

(define reset-stack (lambda () (set! *stack* '())))

;;; The examples start here:

;;; Factorial

(define fact-1
  (letrec ((fact
	    (lambda (n)
	      (if (zero? n)
		  1
		  (* n (fact (- n 1)))))))
    fact))

(define fact-2
  (letrec ((fact
	    (lambda (n k)
	      (if (zero? n)
		  (k 1)
		  (fact (- n 1)
			(lambda (x)
			  (k (* n x))))))))
    (lambda (n)
      (fact n (lambda (x) x)))))

(define fact-3
  (letrec ((fact
	    (lambda (n k)
	      (if (zero? n)
		  (apply-k k 1)
		  (fact (- n 1)
			(make-k-fact n k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-fact (lambda (n k) (lambda (x) (apply-k k (* n x))))))
    (lambda (n)
      (fact n (make-k-init)))))

(define fact-4
  (letrec ((fact
	    (lambda (n k)
	      (if (zero? n)
		  (apply-k k 1)
		  (fact (- n 1)
			(make-k-fact n k)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-fact)
			 (with k-fields
			   (lambda (n k)
			     (apply-k k (* n x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fact (lambda (n k) `(k-fact ,n ,k))))
    (lambda (n)
      (fact n (make-k-init)))))

(define fact-5
  (letrec ((fact
	    (lambda (n k)
	      (if (zero? n)
		  (apply-k k 1)
		  (fact (- n 1)
			(make-k-fact n k)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-fact)
			 (with k-fields
			   (lambda (n . k)
			     (apply-k k (* n x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fact (lambda (n k) `(k-fact ,n . ,k))))
    (lambda (n)
      (fact n (make-k-init)))))

(define fact-6
  ;; these are the registers
  (let ((n 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((fact
	      (lambda ()
		(if (zero? n)
		    (begin
		      (set! x 1)
		      (set! k (pop))
		      (apply-k))
		    (begin
		      (push n)
		      (set! n (- n 1))
		      (push 'k-fact)
		      (fact)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-fact)
		       (set! n (pop))
		       (set! x (* n x))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_n)
	(set! n _n)
	(reset-stack)
	(push 'k-init)
	(fact)))))

;;; Fibonacci

(define fib-1
  (letrec ((fib
	    (lambda (n)
	      (if (< n 2)
		  n
		  (+ (fib (- n 1))
		     (fib (- n 2)))))))
    fib))

(define fib-2
  (letrec ((fib
	    (lambda (n k)
	      (if (< n 2)
		  (k n)
		  (fib (- n 1)
		       (lambda (x)
			 (fib (- n 2)
			      (lambda (y)
				(k (+ x y))))))))))
    (lambda (n)
      (fib n (lambda (x) x)))))

(define fib-3
  (letrec ((fib
	    (lambda (n k)
	      (if (< n 2)
		  (apply-k k n)
		  (fib (- n 1)
		       (make-k-fib-1 n k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-fib-1
	    (lambda (n k)
	      (lambda (x)
		(fib (- n 2)
		     (make-k-fib-2 x k)))))
	   (make-k-fib-2
	    (lambda (y k)
	      (lambda (x)
		(apply-k k (+ x y))))))
    (lambda (n)
      (fib n (make-k-init)))))

(define fib-4
  (letrec ((fib
	    (lambda (n k)
	      (if (< n 2)
		  (apply-k k n)
		  (fib (- n 1)
		       (make-k-fib-1 n k)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-fib-1)
			 (with k-fields
			   (lambda (n k)
			     (fib (- n 2)
				  (make-k-fib-2 x k)))))
			((eq? (car k) 'k-fib-2)
			 (with k-fields
			   (lambda (y k)
			     (apply-k k (+ x y)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fib-1 (lambda (n k) `(k-fib-1 ,n ,k)))
	   (make-k-fib-2 (lambda (y k) `(k-fib-2 ,y ,k))))
    (lambda (n)
      (fib n (make-k-init)))))

(define fib-5
  (letrec ((fib
	    (lambda (n k)
	      (if (< n 2)
		  (apply-k k n)
		  (fib (- n 1)
		       (make-k-fib-1 n k)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-fib-1)
			 (with k-fields
			   (lambda (n . k)
			     (fib (- n 2)
				  (make-k-fib-2 x k)))))
			((eq? (car k) 'k-fib-2)
			 (with k-fields
			   (lambda (y . k)
			     (apply-k k (+ x y)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fib-1 (lambda (n k) `(k-fib-1 ,n . ,k)))
	   (make-k-fib-2 (lambda (y k) `(k-fib-2 ,y . ,k))))
    (lambda (n)
      (fib n (make-k-init)))))

(define fib-6
  ;; these are the registers
  (let ((n 'moshe)
	(k 'moshe)
	(x 'moshe)
	(y 'moshe))
    (letrec ((fib
	      (lambda ()
		(if (< n 2)
		    (begin
		      (set! x n)
		      (set! k (pop))
		      (apply-k))
		    (begin
		      (push n)
		      (set! n (- n 1))
		      (push 'k-fib-1)
		      (fib)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-fib-1)
		       (set! n (pop))
		       (push x)
		       (set! n (- n 2))
		       (push 'k-fib-2)
		       (fib))
		      ((eq? k 'k-fib-2)
		       (set! y (pop))
		       (set! x (+ x y))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_n)
	(set! n _n)
	(reset-stack)
	(push 'k-init)
	(fib)))))

(define ack-1
  (letrec ((ack
	    (lambda (a b)
	      (cond ((zero? a) (+ b 1))
		    ((zero? b) (ack (- a 1) 1))
		    (else (ack (- a 1)
			       (ack a (- b 1))))))))
    ack))

(define ack-2
  (letrec ((ack
	    (lambda (a b k)
	      (cond ((zero? a) (k (+ b 1)))
		    ((zero? b) (ack (- a 1) 1 k))
		    (else (ack a (- b 1)
			       (lambda (x)
				 (ack (- a 1) x k))))))))
    (lambda (a b)
      (ack a b (lambda (x) x)))))

(define ack-3
  (letrec ((ack
	    (lambda (a b k)
	      (cond ((zero? a) (apply-k k (+ b 1)))
		    ((zero? b) (ack (- a 1) 1 k))
		    (else (ack a (- b 1) (make-k-ack a k))))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-ack (lambda (a k) (lambda (x) (ack (- a 1) x k)))))
    (lambda (a b)
      (ack a b (make-k-init)))))

(define ack-4
  (letrec ((ack
	    (lambda (a b k)
	      (cond ((zero? a) (apply-k k (+ b 1)))
		    ((zero? b) (ack (- a 1) 1 k))
		    (else (ack a (- b 1) (make-k-ack a k))))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-ack)
			 (with k-fields
			   (lambda (a k)
			     (ack (- a 1) x k))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-ack (lambda (a k) `(k-ack ,a ,k))))
    (lambda (a b)
      (ack a b (make-k-init)))))

(define ack-5
  (letrec ((ack
	    (lambda (a b k)
	      (cond ((zero? a) (apply-k k (+ b 1)))
		    ((zero? b) (ack (- a 1) 1 k))
		    (else (ack a (- b 1) (make-k-ack a k))))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-ack)
			 (with k-fields
			   (lambda (a . k)
			     (ack (- a 1) x k))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-ack (lambda (a k) `(k-ack ,a . ,k))))
    (lambda (a b)
      (ack a b (make-k-init)))))

(define ack-6
  ;; these are the registers
  (let ((a 'moshe)
	(b 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((ack
	      (lambda ()
		(cond ((zero? a)
		       (set! x (+ b 1))
		       (set! k (pop))
		       (apply-k))
		      ((zero? b)
		       (set! b 1)
		       (set! a (- a 1))
		       (ack))
		      (else
		       (push a)
		       (set! b (- b 1))
		       (push 'k-ack)
		       (ack)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-ack)
		       (set! a (pop))
		       (set! b x)
		       (set! a (- a 1))
		       (ack))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_a _b)
	(set! a _a)
	(set! b _b)
	(reset-stack)
	(push 'k-init)
	(ack)))))

;;; Length

(define length-1
  (letrec ((length
	    (lambda (s)
	      (if (null? s)
		  0
		  (+ 1 (length (cdr s)))))))
    length))

(define length-2
  (letrec ((length
	    (lambda (s k)
	      (if (null? s)
		  (k 0)
		  (length (cdr s)
			  (lambda (x)
			    (k (+ x 1))))))))
    (lambda (s)
      (length s (lambda (x) x)))))

(define length-3
  (letrec ((length
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k 0)
		  (length (cdr s)
			  (make-k-length k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-length (lambda (k) (lambda (x) (apply-k k (+ x 1))))))
    (lambda (s)
      (length s (make-k-init)))))

(define length-4
  (letrec ((length
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k 0)
		  (length (cdr s)
			  (make-k-length k)))))
	   (apply-k 
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-length)
			 (with k-fields
			   (lambda (k)
			     (apply-k k (+ x 1)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-length (lambda (k) `(k-length ,k))))
    (lambda (s)
      (length s (make-k-init)))))

(define length-5
  (letrec ((length
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k 0)
		  (length (cdr s)
			  (make-k-length k)))))
	   (apply-k 
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-length)
			 (with k-fields
			   (lambda k
			     (apply-k k (+ x 1)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-length (lambda (k) `(k-length . ,k))))
    (lambda (s)
      (length s (make-k-init)))))

(define length-6
  ;; these are the registers
  (let ((s 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((length
	      (lambda ()
		(if (null? s)
		    (begin
		      (set! x 0)
		      (set! k (pop))
		      (apply-k))
		    (begin
		      (push 'k-length)
		      (set! s (cdr s))
		      (length)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-length)
		       (set! x (+ x 1))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_s)
	(set! s _s)
	(reset-stack)
	(push 'k-init)
	(length)))))

;;; Flat replace-first

(define replace-first-1
  (letrec ((rep
	    (lambda (a b s)
	      (cond ((null? s) '())
		    ((eq? (car s) a)
		     (cons b (cdr s)))
		    (else (cons (car s)
			    (rep a b (cdr s))))))))
    rep))

(define replace-first-2
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (k '()))
		    ((eq? (car s) a)
		     (k (cons b (cdr s))))
		    (else (rep a b (cdr s)
			       (lambda (x)
				 (k (cons (car s) x)))))))))
    (lambda (a b s)
      (rep a b s (lambda (x) x)))))

(define replace-first-3
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (apply-k k (cons b (cdr s))))
		    (else (rep a b (cdr s)
			       (make-k-rep s k))))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-rep
	    (lambda (s k)
	      (lambda (x)
		(apply-k k (cons (car s) x))))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-first-4
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (apply-k k (cons b (cdr s))))
		    (else (rep a b (cdr s)
			       (make-k-rep s k))))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-rep)
			 (with k-fields
			   (lambda (s k)
			     (apply-k k (cons (car s) x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-rep (lambda (s k) `(k-rep ,s ,k))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-first-5
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (apply-k k (cons b (cdr s))))
		    (else (rep a b (cdr s)
			       (make-k-rep s k))))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-rep)
			 (with k-fields
			   (lambda (s . k)
			     (apply-k k (cons (car s) x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-rep (lambda (s k) `(k-rep ,s . ,k))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-first-6
  ;; these are the registers
  (let ((a 'moshe)
	(b 'moshe)
	(s 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((rep
	      (lambda ()
		(cond ((null? s)
		       (set! x '())
		       (set! k (pop))
		       (apply-k))
		      ((eq? (car s) a)
		       (set! x (cons b (cdr s)))
		       (set! k (pop))
		       (apply-k))
		      (else (push s)
			    (push 'k-rep)
			    (set! s (cdr s))
			    (rep)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-rep)
		       (set! s (pop))
		       (set! x (cons (car s) x))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_a _b _s)
	(set! a _a)
	(set! b _b)
	(set! s _s)
	(reset-stack)
	(push 'k-init)
	(rep)))))

;;; Replacing all occurrences of a in s with b; s is a flat list

(define replace-all-flat-1
  (letrec ((rep
	    (lambda (a b s)
	      (cond ((null? s) '())
		    ((eq? (car s) a)
		     (cons b (rep a b (cdr s))))
		    (else (cons (car s) (rep a b (cdr s))))))))
    rep))

(define replace-all-flat-2
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (k '()))
		    ((eq? (car s) a)
		     (rep a b (cdr s)
			  (lambda (x)
			    (k (cons b x)))))
		    (else (rep a b (cdr s)
			       (lambda (x)
				 (k (cons (car s) x)))))))))
    (lambda (a b s)
      (rep a b s (lambda (x) x)))))

(define replace-all-flat-3
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (rep a b (cdr s)
			  (make-k-rep-1 b k)))
		    (else (rep a b (cdr s)
			       (make-k-rep-2 s k))))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-rep-1 (lambda (b k) (lambda (x) (apply-k k (cons b x)))))
	   (make-k-rep-2 (lambda (s k) (lambda (x) (apply-k k (cons (car s) x))))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-all-flat-4
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (rep a b (cdr s)
			  (make-k-rep-1 b k)))
		    (else (rep a b (cdr s)
			       (make-k-rep-2 s k))))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-rep-1)
			 (with k-fields
			   (lambda (b k)
			     (apply-k k (cons b x)))))
			((eq? (car k) 'k-rep-2)
			 (with k-fields
			   (lambda (s k)
			     (apply-k k (cons (car s) x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-rep-1 (lambda (b k) `(k-rep-1 ,b ,k)))
	   (make-k-rep-2 (lambda (s k) `(k-rep-2 ,s ,k))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-all-flat-5
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (rep a b (cdr s)
			  (make-k-rep-1 b k)))
		    (else (rep a b (cdr s)
			       (make-k-rep-2 s k))))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-rep-1)
			 (with k-fields
			   (lambda (b . k)
			     (apply-k k (cons b x)))))
			((eq? (car k) 'k-rep-2)
			 (with k-fields
			   (lambda (s . k)
			     (apply-k k (cons (car s) x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-rep-1 (lambda (b k) `(k-rep-1 ,b . ,k)))
	   (make-k-rep-2 (lambda (s k) `(k-rep-2 ,s . ,k))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-all-flat-6
  ;; these are the registers
  (let ((a 'moshe)
	(b 'moshe)
	(s 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((rep
	      (lambda ()
		(cond ((null? s)
		       (set! x '())
		       (set! k (pop))
		       (apply-k))
		      ((eq? (car s) a)
		       (push b)
		       (push 'k-rep-1)
		       (set! s (cdr s))
		       (rep))
		      (else (push s)
			    (push 'k-rep-2)
			    (set! s (cdr s))
			    (rep)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-rep-1)
		       (set! b (pop))
		       (set! x (cons b x))
		       (set! k (pop))
		       (apply-k))
		      ((eq? k 'k-rep-2)
		       (set! s (pop))
		       (set! x (cons (car s) x))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_a _b _s)
	(set! a _a)
	(set! b _b)
	(set! s _s)
	(reset-stack)
	(push 'k-init)
	(rep)))))

;;; Solving the Towers of Hanoi

(define hanoi-1
  (letrec ((hanoi
	    (lambda (n from to using)
	      (if (zero? n)
		  '()
		  `(,@(hanoi (- n 1) from using to)
		    (move a disk from ,from to ,to)
		    ,@(hanoi (- n 1) using to from))))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c))))

(define hanoi-2
  (letrec ((hanoi
	    (lambda (n from to using k)
	      (if (zero? n)
		  (k '())
		  (hanoi (- n 1) from using to
			 (lambda (x)
			   (hanoi (- n 1) using to from
				  (lambda (y)
				    (k `(,@x
					 (move a disk from ,from to ,to)
					 ,@y))))))))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c (lambda (x) x)))))

(define hanoi-3
  (letrec ((hanoi
	    (lambda (n from to using k)
	      (if (zero? n)
		  (apply-k k '())
		  (hanoi (- n 1) from using to
			 (make-k-hanoi-1 n from to using k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-hanoi-1
	    (lambda (n from to using k)
	      (lambda (x)
		(hanoi (- n 1) using to from
		       (make-k-hanoi-2 x from to k)))))
	   (make-k-hanoi-2
	    (lambda (x from to k)
	      (lambda (y)
		(apply-k k `(,@x (move a disk from ,from to ,to) ,@y))))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c (make-k-init)))))

(define hanoi-4
  (letrec ((hanoi
	    (lambda (n from to using k)
	      (if (zero? n)
		  (apply-k k '())
		  (hanoi (- n 1) from using to
			 (make-k-hanoi-1 n from to using k)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tags . k-fields)
		  (cond ((eq? k-tags 'k-init) x)
			((eq? k-tags 'k-hanoi-1)
			 (with k-fields
			   (lambda (n from to using k)
			     (hanoi (- n 1) using to from
				    (make-k-hanoi-2 x from to k)))))
			((eq? (car k) 'k-hanoi-2)
			 (with k-fields
			   (lambda (y from to k)
			     (apply-k
			      k
			      `(,@y
				(move a disk from ,from to ,to)
				,@x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init
	    (lambda () `(k-init)))
	   (make-k-hanoi-1
	    (lambda (n from to using k) `(k-hanoi-1 ,n ,from ,to ,using ,k)))
	   (make-k-hanoi-2
	    (lambda (x from to k) `(k-hanoi-2 ,x ,from ,to ,k))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c (make-k-init)))))

(define hanoi-5
  (letrec ((hanoi
	    (lambda (n from to using k)
	      (if (zero? n)
		  (apply-k k '())
		  (hanoi (- n 1) from using to
			 (make-k-hanoi-1 n from to using k)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-hanoi-1)
			 (with k-fields
			   (lambda (n from to using . k)
			     (hanoi (- n 1) using to from
				    (make-k-hanoi-2 x from to k)))))
			((eq? (car k) 'k-hanoi-2)
			 (with k-fields
			   (lambda (y from to . k)
			     (apply-k k `(,@y
					  (move a disk from ,from to ,to)
					  ,@x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-hanoi-1 (lambda (n from to using k) `(k-hanoi-1 ,n ,from ,to ,using . ,k)))
	   (make-k-hanoi-2 (lambda (x from to k) `(k-hanoi-2 ,x ,from ,to . ,k))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c (make-k-init)))))

(define hanoi-6
  ;; these are the registers
  (let ((n 'moshe)
	(from 'moshe)
	(to 'moshe)
	(using 'moshe)
	(k 'moshe)
	(x 'moshe)
	(y 'moshe)
	(tmp 'moshe))
    (letrec ((hanoi
	      (lambda ()
		(if (zero? n)
		    (begin
		      (set! x '())
		      (set! k (pop))
		      (apply-k))
		    (begin
		      (push using)
		      (push to)
		      (push from)
		      (push n)
		      (push 'k-hanoi-1)
		      (set! tmp to)
		      (set! to using)
		      (set! using tmp)
		      (set! n (- n 1))
		      (hanoi)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-hanoi-1)
		       (set! n (pop))
		       (set! from (pop))
		       (set! to (pop))
		       (set! using (pop))
		       (push to)
		       (push from)
		       (push x)
		       (push 'k-hanoi-2)
		       (set! tmp from)
		       (set! from using)
		       (set! using tmp)
		       (set! n (- n 1))
		       (hanoi))
		      ((eq? k 'k-hanoi-2)
		       (set! y (pop))
		       (set! from (pop))
		       (set! to (pop))
		       (set! x `(,@y (move a disk from ,from to ,to) ,@x))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_n)
	(set! n _n)
	(reset-stack)
	(push 'k-init)
	(set! from 'peg-a)
	(set! to 'peg-b)
	(set! using 'peg-c)
	(hanoi)))))

;;; Fast Fibonacci

;;; fast-fib-1 doesn't exist, because fast-fib is originally written in CPS

(define fast-fib-2
  (letrec ((run
	    (lambda (a b c d n k)
	      (if (zero? n)
		  (k 1 0 0 1)
		  (run a b c d (quotient n 2)
		       (lambda (a b c d)
			 (let ((b*c (* b c))
			       (a+d (+ a d)))
			   (let ((a (+ (* a a) b*c))
				 (b (* b a+d))
				 (c (* c a+d))
				 (d (+ b*c (* d d))))
			     (if (even? n)
				 (k a b c d)
				 (k (+ a c) (+ b d) a b))))))))))
    (lambda (n)
      (run 1 1 1 0 n
	   (lambda (fib-n+1 fib-n _fib-n fib-n-1)
	     fib-n)))))

(define fast-fib-3
  (letrec ((run
	    (lambda (a b c d n k)
	      (if (zero? n)
		  (apply-k k 1 0 0 1)
		  (run a b c d (quotient n 2)
		       (make-k-fib n k)))))
	   (apply-k
	    (lambda (k a b c d)
	      (k a b c d)))
	   (make-k-init (lambda () (lambda (a b c d) b)))
	   (make-k-fib
	    (lambda (n k)
	      (lambda (a b c d)
		(let ((b*c (* b c))
		      (a+d (+ a d)))
		  (let ((a (+ (* a a) b*c))
			(b (* b a+d))
			(c (* c a+d))
			(d (+ b*c (* d d))))
		    (if (even? n)
			(apply-k k a b c d)
			(apply-k k (+ a c) (+ b d) a b))))))))
    (lambda (n)
      (run 1 1 1 0 n (make-k-init)))))

(define fast-fib-4
  (letrec ((run
	    (lambda (a b c d n k)
	      (if (zero? n)
		  (apply-k k 1 0 0 1)
		  (run a b c d (quotient n 2)
		       (make-k-fib n k)))))
	   (apply-k
	    (lambda (k a b c d)
	      (cond ((eq? (car k) 'k-init) b)
		    ((eq? (car k) 'k-fib)
		     (with k
		       (lambda (_k n k)
			 (let ((b*c (* b c))
			       (a+d (+ a d)))
			   (let ((a (+ (* a a) b*c))
				 (b (* b a+d))
				 (c (* c a+d))
				 (d (+ b*c (* d d))))
			     (if (even? n)
				 (apply-k k a b c d)
				 (apply-k k (+ a c) (+ b d) a b)))))))
		    (else (error 'apply-k
			    "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fib (lambda (n k) `(k-fib ,n ,k))))
    (lambda (n)
      (run 1 1 1 0 n (make-k-init)))))

(define fast-fib-5
  (letrec ((run
	    (lambda (a b c d n k)
	      (if (zero? n)
		  (apply-k k 1 0 0 1)
		  (run a b c d (quotient n 2)
		       (make-k-fib n k)))))
	   (apply-k
	    (lambda (k a b c d)
	      (cond ((eq? (car k) 'k-init) b)
		    ((eq? (car k) 'k-fib)
		     (with k
		       (lambda (_k n . k)
			 (let ((b*c (* b c))
			       (a+d (+ a d)))
			   (let ((a (+ (* a a) b*c))
				 (b (* b a+d))
				 (c (* c a+d))
				 (d (+ b*c (* d d))))
			     (if (even? n)
				 (apply-k k a b c d)
				 (apply-k k (+ a c) (+ b d) a b)))))))
		    (else (error 'apply-k
			    "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fib (lambda (n k) `(k-fib ,n . ,k))))
    (lambda (n)
      (run 1 1 1 0 n (make-k-init)))))

(define fast-fib-6
  ;; these are the registers
  (let ((a 'moshe)
	(b 'moshe)
	(c 'moshe)
	(d 'moshe)
	(a+d 'moshe)
	(b*c 'moshe)
	(n 'moshe)
	(k 'moshe))
    (letrec ((run
	      (lambda ()
		(if (zero? n)
		    (begin
		      (set! d 1)
		      (set! c 0)
		      (set! b 0)
		      (set! a 1)
		      (set! k (pop))
		      (apply-k))
		    (begin
		      (push n)
		      (set! n (quotient n 2))
		      (push 'k-fib)
		      (run)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) b)
		      ((eq? k 'k-fib)
		       (set! n (pop))
		       (set! b*c (* b c))
		       (set! a+d (+ a d))
		       (set! d (+ b*c (* d d)))
		       (set! c (* c a+d))
		       (set! b (* b a+d))
		       (set! a (+ (* a a) b*c))
		       (if (even? n)
			   (begin
			     (set! k (pop))
			     (apply-k))
			   (begin
			     (set! tmp1 a)
			     (set! tmp2 b)
			     (set! a (+ a c))
			     (set! b (+ b d))
			     (set! c tmp1)
			     (set! d tmp2)
			     (set! k (pop))
			     (apply-k))))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_n)
	(set! n _n)
	(reset-stack)
	(push 'k-init)
	(run)))))

;;; the power set

(define power-1
  (letrec ((runv
	    (lambda (s)
	      (if (null? s)
		  '(())
		  (let ((w (runv (cdr s))))
		    (append w (runh (car s) w))))))
	   (runh
	    (lambda (a s)
	      (if (null? s)
		  '()
		  (cons (cons a (car s))
		    (runh a (cdr s)))))))
    runv))

(define power-2
  (letrec ((runv
	    (lambda (s k)
	      (if (null? s)
		  (k '(()))
		  (runv (cdr s)
			(lambda (w)
			  (runh (car s) w
				(lambda (x)
				  (k (append w x)))))))))
	   (runh
	    (lambda (a s k)
	      (if (null? s)
		  (k '())
		  (runh a (cdr s)
			(lambda (x)
			  (k (cons (cons a (car s)) x))))))))
    (lambda (s)
      (runv s (lambda (x) x)))))

(define power-3
  (letrec ((runv
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k '(()))
		  (runv (cdr s)
			(make-k-runv-1 s k)))))
	   (runh
	    (lambda (a s k)
	      (if (null? s)
		  (apply-k k '())
		  (runh a (cdr s)
			(make-k-runh a s k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-runv-1
	    (lambda (s k)
	      (lambda (w)
		(runh (car s) w (make-k-runv-2 w k)))))
	   (make-k-runv-2
	    (lambda (w k)
	      (lambda (x) (apply-k k (append w x)))))
	   (make-k-runh
	    (lambda (a s k)
	      (lambda (x)
		(apply-k k (cons (cons a (car s)) x))))))
    (lambda (s)
      (runv s (lambda (x) x)))))

(define power-4
  (letrec ((runv
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k '(()))
		  (runv (cdr s)
			(make-k-runv-1 s k)))))
	   (runh
	    (lambda (a s k)
	      (if (null? s)
		  (apply-k k '())
		  (runh a (cdr s)
			(make-k-runh a s k)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-runv-1)
			 (with k-fields
			   (lambda (s k)
			     (runh (car s) x (make-k-runv-2 x k)))))
			((eq? (car k) 'k-runv-2)
			 (with k-fields
			   (lambda (w k)
			     (apply-k k (append w x)))))
			((eq? (car k) 'k-runh)
			 (with k-fields
			   (lambda (a s k)
			     (apply-k k (cons (cons a (car s)) x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-runv-1 (lambda (s k) `(k-runv-1 ,s ,k)))
	   (make-k-runv-2 (lambda (w k) `(k-runv-2 ,w ,k)))
	   (make-k-runh (lambda (a s k) `(k-runh ,a ,s ,k))))
    (lambda (s)
      (runv s (make-k-init)))))

(define power-5
  (letrec ((runv
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k '(()))
		  (runv (cdr s)
			(make-k-runv-1 s k)))))
	   (runh
	    (lambda (a s k)
	      (if (null? s)
		  (apply-k k '())
		  (runh a (cdr s)
			(make-k-runh a s k)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-runv-1)
			 (with k-fields
			   (lambda (s . k)
			     (runh (car s) x (make-k-runv-2 x k)))))
			((eq? (car k) 'k-runv-2)
			 (with k-fields
			   (lambda (w . k)
			     (apply-k k (append w x)))))
			((eq? (car k) 'k-runh)
			 (with k-fields
			   (lambda (a s . k)
			     (apply-k k (cons (cons a (car s)) x)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-runv-1 (lambda (s k) `(k-runv-1 ,s . ,k)))
	   (make-k-runv-2 (lambda (w k) `(k-runv-2 ,w . ,k)))
	   (make-k-runh (lambda (a s k) `(k-runh ,a ,s . ,k))))
    (lambda (s)
      (runv s (make-k-init)))))

(define power-6
  (let ((s 'moshe)
	(k 'moshe)
	(a 'moshe)
	(w 'moshe)
	(x 'moshe))
    (letrec ((runv
	      (lambda ()
		(if (null? s)
		    (begin
		      (set! x '(()))
		      (set! k (pop))
		      (apply-k))
		    (begin
		      (push s)
		      (set! s (cdr s))
		      (push 'k-runv-1)
		      (runv)))))
	     (runh
	      (lambda ()
		(if (null? s)
		    (begin
		      (set! x '())
		      (set! k (pop))
		      (apply-k))
		    (begin
		      (push s)
		      (push a)
		      (set! s (cdr s))
		      (push 'k-runh)
		      (runh)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-runv-1)
		       (set! s (pop))
		       (push x)
		       (set! a (car s))
		       (set! s x)
		       (push 'k-runv-2)
		       (runh))
		      ((eq? k 'k-runv-2)
		       (set! w (pop))
		       (set! x (append w x))
		       (set! k (pop))
		       (apply-k))
		      ((eq? k 'k-runh)
		       (set! a (pop))
		       (set! s (pop))
		       (set! x (cons (cons a (car s)) x))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_s)
	(set! s _s)
	(reset-stack)
	(push 'k-init)
	(runv)))))

;;; the sine [& cosine] function[s]

(define sin-1
  (let ((epsilon 1.0e-6))
    (letrec ((sin
	      (lambda (x)
		(if (< (abs x) epsilon)
		    x
		    (* 2.0 (sin (/ x 2.0)) (cos (/ x 2.0))))))
	     (cos
	      (lambda (x)
		(if (< (abs x) epsilon)
		    (sqrt (- 1.0 (square x)))
		    (- (square (cos (/ x 2.0)))
		       (square (sin (/ x 2.0)))))))
	     (square
	      (lambda (x)
		(* x x))))
      sin)))

(define sin-2
  (let ((epsilon 1.0e-6))
    (letrec ((sin-k
	      (lambda (x k)
		(if (< (abs x) epsilon)
		    (k x)
		    (sin-k (/ x 2.0)
			   (lambda (sin-x/2)
			     (cos-k (/ x 2.0)
				    (lambda (cos-x/2)
				      (k (* 2.0 sin-x/2 cos-x/2)))))))))
	     (cos-k
	      (lambda (x k)
		(if (< (abs x) epsilon)
		    (square-k x
			      (lambda (x^2)
				(k (sqrt (- 1.0 x^2)))))
		    (cos-k
		     (/ x 2.0)
		     (lambda (cos-x/2)
		       (square-k
			cos-x/2
			(lambda (cos^2-x/2)
			  (sin-k
			   (/ x 2.0)
			   (lambda (sin-x/2)
			     (square-k
			      sin-x/2
			      (lambda (sin^2-x/2)
				(k (- cos^2-x/2 sin^2-x/2)))))))))))))
	     (square-k
	      (lambda (x k)
		(k (* x x)))))
      (lambda (x)
	(sin-k x (lambda (x) x))))))

(define sin-3
  (let ((epsilon 1.0e-6))
    (letrec ((sin-k
	      (lambda (x k)
		(if (< (abs x) epsilon)
		    (apply-k k x)
		    (sin-k
		     (/ x 2.0)
		     (make-k-sin-1 x k)))))
	     (cos-k
	      (lambda (x k)
		(if (< (abs x) epsilon)
		    (square-k x
			      (make-k-cos-1 k))
		    (cos-k
		     (/ x 2.0)
		     (make-k-cos-2 x k)))))
	     (square-k
	      (lambda (x k)
		(apply-k k (* x x))))
	     (apply-k (lambda (k x) (k x)))
	     (make-k-init (lambda () (lambda (x) x)))
	     (make-k-sin-1
	      (lambda (x k)
		(lambda (sin-x/2)
		  (cos-k
		   (/ x 2.0)
		   (make-k-sin-2 sin-x/2 k)))))
	     (make-k-sin-2
	      (lambda (sin-x/2 k)
		(lambda (cos-x/2)
		  (apply-k k (* 2.0 sin-x/2 cos-x/2)))))
	     (make-k-cos-1
	      (lambda (k)
		(lambda (x^2)
		  (apply-k k (sqrt (- 1.0 x^2))))))
	     (make-k-cos-2
	      (lambda (x k)
		(lambda (cos-x/2)
		  (square-k
		   cos-x/2
		   (make-k-cos-3 x k)))))
	     (make-k-cos-3
	      (lambda (x k)
		(lambda (cos^2-x/2)
		  (sin-k
		   (/ x 2.0)
		   (make-k-cos-4 cos^2-x/2 k)))))
	     (make-k-cos-4
	      (lambda (cos^2-x/2 k)	
		(lambda (sin-x/2)
		  (square-k
		   sin-x/2
		   (make-k-cos-5 cos^2-x/2 k)))))
	     (make-k-cos-5
	      (lambda (cos^2-x/2 k)
		(lambda (sin^2-x/2)
		  (apply-k k (- cos^2-x/2 sin^2-x/2))))))
      (lambda (x)
	(sin-k x (make-k-init))))))

(define sin-4
  (let ((epsilon 1.0e-6))
    (letrec ((sin-k
	      (lambda (x k)
		(if (< (abs x) epsilon)
		    (apply-k k x)
		    (sin-k
		     (/ x 2.0)
		     (make-k-sin-1 x k)))))
	     (cos-k
	      (lambda (x k)
		(if (< (abs x) epsilon)
		    (square-k x
			      (make-k-cos-1 k))
		    (cos-k
		     (/ x 2.0)
		     (make-k-cos-2 x k)))))
	     (square-k
	      (lambda (x k)
		(apply-k k (* x x))))
	     (apply-k
	      (lambda (k x)
		(with k
		  (lambda (k-tag . k-fields)
		    (cond ((eq? k-tag 'k-init) x)
			  ((eq? k-tag 'k-sin-1)
			   (with k-fields
			     (lambda (orig-x k)
			       (cos-k
				(/ orig-x 2.0)
				(make-k-sin-2 x k)))))
			  ((eq? k-tag 'k-sin-2)
			   (with k-fields
			     (lambda (sin-x/2 k)
			       (apply-k k (* 2.0 sin-x/2 x)))))
			  ((eq? k-tag 'k-cos-1)
			   (with k-fields
			     (lambda (k)
			       (apply-k k (sqrt (- 1.0 x))))))
			  ((eq? k-tag 'k-cos-2)
			   (with k-fields
			     (lambda (orig-x k)
			       (square-k x (make-k-cos-3 orig-x k)))))
			  ((eq? k-tag 'k-cos-3)
			   (with k-fields
			     (lambda (orig-x k)
			       (sin-k (/ orig-x 2.0) (make-k-cos-4 x k)))))
			  ((eq? k-tag 'k-cos-4)
			   (with k-fields
			     (lambda (cos^2-x/2 k)
			       (square-k x (make-k-cos-5 cos^2-x/2 k)))))
			  ((eq? k-tag 'k-cos-5)
			   (with k-fields
			     (lambda (cos^2-x/2 k)
			       (apply-k k (- cos^2-x/2 x)))))
			  (else (error 'apply-k
				  "Unknown continuation")))))))
	     (make-k-init (lambda () `(k-init)))
	     (make-k-sin-1 (lambda (x k) `(k-sin-1 ,x ,k)))
	     (make-k-sin-2 (lambda (sin-x/2 k) `(k-sin-2 ,sin-x/2 ,k)))
	     (make-k-cos-1 (lambda (k) `(k-cos-1 ,k)))
	     (make-k-cos-2 (lambda (x k) `(k-cos-2 ,x ,k)))
	     (make-k-cos-3 (lambda (x k) `(k-cos-3 ,x ,k)))
	     (make-k-cos-4 (lambda (cos^2-x/2 k) `(k-cos-4 ,cos^2-x/2 ,k)))
	     (make-k-cos-5 (lambda (cos^2-x/2 k) `(k-cos-5 ,cos^2-x/2 ,k))))
      (lambda (x)
	(sin-k x (make-k-init))))))

(define sin-5
  (let ((epsilon 1.0e-6))
    (letrec ((sin-k
	      (lambda (x k)
		(if (< (abs x) epsilon)
		    (apply-k k x)
		    (sin-k
		     (/ x 2.0)
		     (make-k-sin-1 x k)))))
	     (cos-k
	      (lambda (x k)
		(if (< (abs x) epsilon)
		    (square-k x
			      (make-k-cos-1 k))
		    (cos-k
		     (/ x 2.0)
		     (make-k-cos-2 x k)))))
	     (square-k
	      (lambda (x k)
		(apply-k k (* x x))))
	     (apply-k
	      (lambda (k x)
		(with k
		  (lambda (k-tag . k-fields)
		    (cond ((eq? k-tag 'k-init) x)
			  ((eq? k-tag 'k-sin-1)
			   (with k-fields
			     (lambda (orig-x . k)
			       (cos-k
				(/ orig-x 2.0)
				(make-k-sin-2 x k)))))
			  ((eq? k-tag 'k-sin-2)
			   (with k-fields
			     (lambda (sin-x/2 . k)
			       (apply-k k (* 2.0 sin-x/2 x)))))
			  ((eq? k-tag 'k-cos-1)
			   (with k-fields
			     (lambda k
			       (apply-k k (sqrt (- 1.0 x))))))
			  ((eq? k-tag 'k-cos-2)
			   (with k-fields
			     (lambda (orig-x . k)
			       (square-k x (make-k-cos-3 orig-x k)))))
			  ((eq? k-tag 'k-cos-3)
			   (with k-fields
			     (lambda (orig-x . k)
			       (sin-k (/ orig-x 2.0) (make-k-cos-4 x k)))))
			  ((eq? k-tag 'k-cos-4)
			   (with k-fields
			     (lambda (cos^2-x/2 . k)
			       (square-k x (make-k-cos-5 cos^2-x/2 k)))))
			  ((eq? k-tag 'k-cos-5)
			   (with k-fields
			     (lambda (cos^2-x/2 . k)
			       (apply-k k (- cos^2-x/2 x)))))
			  (else (error 'apply-k
				  "Unknown continuation")))))))
	     (make-k-init (lambda () `(k-init)))
	     (make-k-sin-1 (lambda (x k) `(k-sin-1 ,x . ,k)))
	     (make-k-sin-2 (lambda (sin-x/2 k) `(k-sin-2 ,sin-x/2 . ,k)))
	     (make-k-cos-1 (lambda (k) `(k-cos-1 . ,k)))
	     (make-k-cos-2 (lambda (x k) `(k-cos-2 ,x . ,k)))
	     (make-k-cos-3 (lambda (x k) `(k-cos-3 ,x . ,k)))
	     (make-k-cos-4 (lambda (cos^2-x/2 k) `(k-cos-4 ,cos^2-x/2 . ,k)))
	     (make-k-cos-5 (lambda (cos^2-x/2 k) `(k-cos-5 ,cos^2-x/2 . ,k))))
      (lambda (x)
	(sin-k x (make-k-init))))))

(define sin-6
  (let ((epsilon 1.0e-6)
	(x 'moshe)
	(k 'moshe)
	(orig-x 'moshe)
	(sin-x/2 'moshe)
	(cos^2-x/2 'moshe)
	)
    (letrec ((sin
	      (lambda ()
		(if (< (abs x) epsilon)
		    (begin
		      (set! k (pop))
		      (apply-k))
		    (begin
		      (push x)
		      (set! x (/ x 2.0))
		      (push 'k-sin-1)
		      (sin)))))
	     (cos
	      (lambda ()
		(if (< (abs x) epsilon)
		    (begin
		      (push 'k-cos-1)
		      (square))
		    (begin
		      (push x)
		      (set! x (/ x 2.0))
		      (push 'k-cos-2)
		      (cos)))))
	     (square
	      (lambda ()
		(set! x (* x x))
		(set! k (pop))
		(apply-k)))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-sin-1)
		       (set! orig-x (pop))
		       (push x)
		       (set! x (/ orig-x 2.0))
		       (push 'k-sin-2)
		       (cos))
		      ((eq? k 'k-sin-2)
		       (set! sin-x/2 (pop))
		       (set! x (* 2.0 sin-x/2 x))
		       (set! k (pop))
		       (apply-k))
		      ((eq? k 'k-cos-1)
		       (set! x (sqrt (- 1.0 x)))
		       (set! k (pop))
		       (apply-k))
		      ((eq? k 'k-cos-2)
					;(set! orig-x (pop))
					;(push orig-x)
		       (push 'k-cos-3)
		       (square))
		      ((eq? k 'k-cos-3)
		       (set! orig-x (pop))
		       (push x)
		       (set! x (/ orig-x 2.0))
		       (push 'k-cos-4)
		       (sin))
		      ((eq? k 'k-cos-4)
					; (set! cos^2-x/2 (pop))
					; (push cos^2-x/2)
		       (push 'k-cos-5)
		       (square))
		      ((eq? k 'k-cos-5)
		       (set! cos^2-x/2 (pop))
		       (set! x (- cos^2-x/2 x))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_x)
	(set! x _x)
	(reset-stack)
	(push 'k-init)
	(sin)))))

;;; sum
(define sum-1
  (letrec ((run
	    (lambda (e)
	      (cond ((pair? e)
		     (+ (run (car e))
			(run (cdr e))))
		    ((number? e) e)
		    (else 0)))))
    run))

(define sum-2
  (letrec ((run
	    (lambda (e k)
	      (cond ((pair? e)
		     (run (car e)
			  (lambda (x)
			    (run (cdr e)
				 (lambda (y)
				   (k (+ x y)))))))
		    ((number? e) (k e))
		    (else (k 0))))))
    (lambda (e)
      (run e (lambda (x) x)))))

(define sum-3
  (letrec ((run
	    (lambda (e k)
	      (cond ((pair? e)
		     (run (car e)
			  (make-k-run-car e k)))
		    ((number? e) (apply-k k e))
		    (else (apply-k k 0)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-run-car
	    (lambda (e k)
	      (lambda (x)
		(run (cdr e)
		     (make-k-run-cdr x k)))))
	   (make-k-run-cdr
	    (lambda (y k)
	      (lambda (x)
		(apply-k k (+ x y))))))
    (lambda (e)
      (run e (make-k-init)))))

(define sum-4
  (letrec ((run
	    (lambda (e k)
	      (cond ((pair? e)
		     (run (car e)
			  (make-k-run-car e k)))
		    ((number? e) (apply-k k e))
		    (else (apply-k k 0)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-run-car)
			 (with k-fields
			   (lambda (e k)
			     (run (cdr e)
				  (make-k-run-cdr x k)))))
			((eq? k-tag 'k-run-cdr)
			 (with k-fields
			   (lambda (y k)
			     (apply-k k (+ x y)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-run-car (lambda (e k) `(k-run-car ,e ,k)))
	   (make-k-run-cdr (lambda (y k) `(k-run-cdr ,y ,k))))
    (lambda (e)
      (run e (make-k-init)))))

(define sum-5
  (letrec ((run
	    (lambda (e k)
	      (cond ((pair? e)
		     (run (car e)
			  (make-k-run-car e k)))
		    ((number? e) (apply-k k e))
		    (else (apply-k k 0)))))
	   (apply-k
	    (lambda (k x)
	      (with k
		(lambda (k-tag . k-fields)
		  (cond ((eq? k-tag 'k-init) x)
			((eq? k-tag 'k-run-car)
			 (with k-fields
			   (lambda (e . k)
			     (run (cdr e)
				  (make-k-run-cdr x k)))))
			((eq? k-tag 'k-run-cdr)
			 (with k-fields
			   (lambda (y . k)
			     (apply-k k (+ x y)))))
			(else (error 'apply-k
				"Unknown continuation")))))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-run-car (lambda (e k) `(k-run-car ,e . ,k)))
	   (make-k-run-cdr (lambda (y k) `(k-run-cdr ,y . ,k))))
    (lambda (e)
      (run e (make-k-init)))))

(define sum-6
  (let ((x 'moshe)
	(y 'moshe)
	(k 'moshe)
	(e 'moshe))
    (letrec ((run
	      (lambda ()
		(cond ((pair? e)
		       (push e)
		       (set! e (car e))
		       (push 'k-run-car)
		       (run))
		      ((number? e)
		       (set! x e)
		       (set! k (pop))
		       (apply-k))
		      (else
		       (set! x 0)
		       (set! k (pop))
		       (apply-k)))))
	     (apply-k
	      (lambda ()
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-run-car)
		       (set! e (pop))
		       (push x)
		       (set! e (cdr e))
		       (push 'k-run-cdr)
		       (run))
		      ((eq? k 'k-run-cdr)
		       (set! y (pop))
		       (set! x (+ x y))
		       (set! k (pop))
		       (apply-k))
		      (else (error 'apply-k
			      "Unknown continuation"))))))
      (lambda (_e)
	(set! e _e)
	(reset-stack)
	(push 'k-init)
	(run)))))

;;; Permutations of a list

(define perm-1
  (letrec ((f (lambda (a s)
                (if (null? s)
                    `((,a))
                    (let ((w (f (car s) (cdr s))))
                      (g a w)))))

           (g (lambda (a w)
                (if (null? w)
                    '()
                    `(,@(h '() a (car w))
                      ,@(g a (cdr w))))))

           (h (lambda (s1 a s2)
                (if (null? s2)
                    `((,@s1 ,a))
                    `((,@s1 ,a ,@s2)
                      ,@(h `(,@s1 ,(car s2)) a (cdr s2)))))))
    (lambda (s)
      (if (null? s)
          '()
          (f (car s) (cdr s))))))

(define perm-2
  (letrec ((f (lambda (a s k)
                (if (null? s)
                    (k `((,a)))
                    (f (car s) (cdr s)
                      (lambda (x)
                        (g a x k))))))
           (g (lambda (a w k)
                (if (null? w)
                    (k '())
                    (h '() a (car w)
                      (lambda (x)
                        (g a (cdr w)
                          (lambda (y)
                            (k `(,@x ,@y)))))))))
           (h (lambda (s1 a s2 k)
                (if (null? s2)
                    (k `((,@s1 ,a)))
                    (h `(,@s1 ,(car s2)) a (cdr s2)
                      (lambda (x)
                        (k `((,@s1 ,a ,@s2) ,@x))))))))
    (lambda (s)
      (if (null? s)
          '()
          (f (car s) (cdr s) (lambda (x) x))))))

(define perm-3
  (letrec ((f (lambda (a s k)
                (if (null? s)
                    (apply-k k `((,a)))
                    (f (car s) (cdr s) (make-k1 a k)))))
           (g (lambda (a w k)
                (if (null? w)
                    (apply-k k '())
                    (h '() a (car w) (make-k2 a w k)))))
           (h (lambda (s1 a s2 k)
                (if (null? s2)
                    (apply-k k `((,@s1 ,a)))
                    (h `(,@s1 ,(car s2)) a (cdr s2)
                      (make-k3 s1 a s2 k)))))
           ;;
           (apply-k (lambda (k x) (k x)))
           (make-k-init (lambda () (lambda (x) x)))
           (make-k1 (lambda (a k) (lambda (x) (g a x k))))
           (make-k2
             (lambda (a w k) (lambda (x) (g a (cdr w) (make-k4 x k)))))
           (make-k3
             (lambda (s1 a s2 k)
               (lambda (x)
                 (apply-k k `((,@s1 ,a ,@s2) ,@x)))))
           (make-k4 (lambda (y k) (lambda (x) (apply-k k `(,@y ,@x))))))
    (lambda (s)
      (if (null? s)
          '()
          (f (car s) (cdr s) (make-k-init))))))

(define perm-4
  (letrec ((f (lambda (a s k)
                (if (null? s)
                    (apply-k k `((,a)))
                    (f (car s) (cdr s) (make-k1 a k)))))
           (g (lambda (a w k)
                (if (null? w)
                    (apply-k k '())
                    (h '() a (car w) (make-k2 a w k)))))
           (h (lambda (s1 a s2 k)
                (if (null? s2)
                    (apply-k k `((,@s1 ,a)))
                    (h `(,@s1 ,(car s2)) a (cdr s2)
                      (make-k3 s1 a s2 k)))))
           ;;
           (apply-k
             (lambda (k x)
               (with k
                 (lambda (k-tag . k-fields)
                   (cond ((eq? k-tag 'k-init) x)
                         ((eq? k-tag 'k1)
                          (with k-fields
                            (lambda (a k)
                              (g a x k))))
                         ((eq? k-tag 'k2)
                          (with k-fields
                            (lambda (a w k)
                              (g a (cdr w) (make-k4 x k)))))
                         ((eq? k-tag 'k3)
                          (with k-fields
                            (lambda (s1 a s2 k)
                              (apply-k k `((,@s1 ,a ,@s2) ,@x)))))
                         ((eq? k-tag 'k4) 
                          (with k-fields
                            (lambda (y k)
                              (apply-k k `(,@y ,@x)))))
                         (else (error 'apply-k
				 "Unknown continuation")))))))
           (make-k-init (lambda () `(k-init)))
           (make-k1 (lambda (a k) `(k1 ,a ,k)))
           (make-k2 (lambda (a w k) `(k2 ,a ,w ,k)))
           (make-k3 (lambda (s1 a s2 k) `(k3 ,s1 ,a ,s2 ,k)))
           (make-k4 (lambda (y k) `(k4 ,y ,k))))
    (lambda (s)
      (if (null? s)
          '()
          (f (car s) (cdr s) (make-k-init))))))

(define perm-5
  (letrec ((f (lambda (a s k)
                (if (null? s)
                    (apply-k k `((,a)))
                    (f (car s) (cdr s) (make-k1 a k)))))
           (g (lambda (a w k)
                (if (null? w)
                    (apply-k k '())
                    (h '() a (car w) (make-k2 a w k)))))
           (h (lambda (s1 a s2 k)
                (if (null? s2)
                    (apply-k k `((,@s1 ,a)))
                    (h `(,@s1 ,(car s2)) a (cdr s2)
                      (make-k3 s1 a s2 k)))))
           ;;
           (apply-k
             (lambda (k x)
               (with k
                 (lambda (k-tag . k-fields)
                   (cond ((eq? k-tag 'k-init) x)
                         ((eq? k-tag 'k1)
                          (with k-fields
                            (lambda (a . k)
                              (g a x k))))
                         ((eq? k-tag 'k2)
                          (with k-fields
                            (lambda (a w . k)
                              (g a (cdr w) (make-k4 x k)))))
                         ((eq? k-tag 'k3)
                          (with k-fields
                            (lambda (s1 a s2 . k)
                              (apply-k k `((,@s1 ,a ,@s2) ,@x)))))
                         ((eq? k-tag 'k4) 
                          (with k-fields
                            (lambda (y . k)
                              (apply-k k `(,@y ,@x)))))
                         (else (error 'apply-k
				 "Unknown continuation")))))))
           (make-k-init (lambda () `(k-init)))
           (make-k1 (lambda (a k) `(k1 ,a . ,k)))
           (make-k2 (lambda (a w k) `(k2 ,a ,w . ,k)))
           (make-k3 (lambda (s1 a s2 k) `(k3 ,s1 ,a ,s2 . ,k)))
           (make-k4 (lambda (y k) `(k4 ,y . ,k))))
    (lambda (s)
      (if (null? s)
          '()
          (f (car s) (cdr s) (make-k-init))))))

(define perm-6
  ;; these are the registers
  (let ((a 'moshe)
        (s 'moshe)
        (s1 'moshe)
        (s2 'moshe)
        (x 'moshe)
        (y 'moshe)
        (w 'moshe))
    (letrec ((f (lambda ()
                  (if (null? s)
                      (begin
                        (set! x `((,a)))
                        (set! k (pop))
                        (apply-k))
                      (begin
                        (push a)
                        (set! a (car s))
                        (set! s (cdr s))
                        (push 'k1)
                        (f)))))
             (g (lambda ()
                  (if (null? w)
                      (begin
                        (set! x '())
                        (set! k (pop))
                        (apply-k))
                      (begin
                        (push w)
                        (push a)
                        (set! s2 (car w))
                        (set! s1 '())
                        (push 'k2)
                        (h)))))
             (h (lambda ()
                  (if (null? s2)
                      (begin
                        (set! x `((,@s1 ,a)))
                        (set! k (pop))
                        (apply-k))
                      (begin
                        (push s2)
                        (push a)
                        (push s1)
                        (set! s1 `(,@s1 ,(car s2)))
                        (set! s2 (cdr s2))
                        (push 'k3)
                        (h)))))
             (apply-k
               (lambda ()
                 (cond ((eq? k 'k-init) x)
                       ((eq? k 'k1)
                        (set! a (pop))
                        (set! w x)
                        (g))
                       ((eq? k 'k2)
                        (set! a (pop))
                        (set! w (pop))
                        (push x)
                        (set! w (cdr w))
                        (push 'k4)
                        (g))
                       ((eq? k 'k3)
                        (set! s1 (pop))
                        (set! a (pop))
                        (set! s2 (pop))
                        (set! x `((,@s1 ,a ,@s2) ,@x))
                        (set! k (pop))
                        (apply-k))
                       ((eq? k 'k4)
                        (set! y (pop))
                        (set! x `(,@y ,@x))
                        (set! k (pop))
                        (apply-k))
                       (else (error 'apply-k
			       "Unknown continuation"))))))
      (lambda (_s)
        (set! s _s)
        (reset-stack)
        (if (null? s)
            '()
            (begin
              (push 'k-init)
              (set! a (car s))
              (set! s (cdr s))
              (f)))))))

;;; Testing

;;; Run (test) --
;;; If you get #t then all is well;
;;; If you get #f or an error message,
;;;   then it is not the case that all is well...

(define test
  (lambda ()
    (and ((lambda facts (andmap (lambda (fact) (= (fact 5) 120)) facts))
	  fact-1 fact-2 fact-3 fact-4 fact-5 fact-6)
	 ((lambda fibs (andmap (lambda (fib) (= (fib 10) 55)) fibs))
	  fib-1 fib-2 fib-3 fib-4 fib-5 fib-6)
	 ((lambda acks (andmap (lambda (ack) (= (ack 3 3) 61)) acks))
	  ack-1 ack-2 ack-3 ack-4 ack-5 ack-6)
	 ((lambda lengths
	    (andmap
	     (lambda (length) (= (length '(a b c d e)) 5)) lengths))
	  length-1 length-2 length-3 length-4 length-5 length-6)
	 ((lambda replace-firsts
	    (andmap
	     (lambda (replace-first)
	       (and (equal? (replace-first 'a 'b '(a b a))
			    '(b b a))
		    (equal? (replace-first 'a 'b '(c))
			    '(c))
		    (equal? (replace-first 'a 'b '(moshe a (a) a))
			    '(moshe b (a) a))))
	     replace-firsts))
	  replace-first-1 replace-first-2 replace-first-3
	  replace-first-4 replace-first-5 replace-first-6)
	 ((lambda replace-all-flats
	    (andmap
	     (lambda (replace-all-flat)
	       (and (equal? (replace-all-flat 'a 'b '(a b a))
			    '(b b b))
		    (equal? (replace-all-flat 'a 'b '(c))
			    '(c))
		    (equal? (replace-all-flat 'a 'b '(moshe a (a) a))
			    '(moshe b (a) b))))
	     replace-all-flats))
	  replace-all-flat-1 replace-all-flat-2 replace-all-flat-3
	  replace-all-flat-4 replace-all-flat-5 replace-all-flat-6)
	 ((lambda hanois
	    (andmap
	     (lambda (hanoi)
	       (equal?
		(hanoi 3)
		'((move a disk from peg-a to peg-b)
		  (move a disk from peg-a to peg-c)
		  (move a disk from peg-b to peg-c)
		  (move a disk from peg-a to peg-b)
		  (move a disk from peg-c to peg-a)
		  (move a disk from peg-c to peg-b)
		  (move a disk from peg-a to peg-b))))
	     hanois))
	  hanoi-1 hanoi-2 hanoi-3 hanoi-4 hanoi-5 hanoi-6)
	 ((lambda fibs (andmap (lambda (fib) (= (fib 10) 55)) fibs))
	  fast-fib-2 fast-fib-3 fast-fib-4 fast-fib-5 fast-fib-6)
	 ((lambda powers
	    (andmap
	     (lambda (power)
	       (equal? (power '(a b c))
		       '(() (c) (b) (b c) (a) (a c) (a b) (a b c))))
	     powers))
	  power-1 power-2 power-3 power-4 power-5 power-6)
	 (let ((=/epsilon
		(let ((epsilon 1.0e-6))
		  (lambda (x y)
		    (< (abs (- x y)) epsilon))))
	       (sin-2.34 (sin 2.34)))
	   ((lambda sins
	      (andmap
	       (lambda (sin) 
		 (=/epsilon (sin 2.34) sin-2.34))
	       sins))
	    sin-1 sin-2 sin-3 sin-4 sin-5 sin-6))
	 ((lambda sums
	    (andmap (lambda (sum)
		      (= (sum '(1 ((1 . 2) (3 . 5)) ((8 13) 21)))
			 54))
		    sums))
	  sum-1 sum-2 sum-3 sum-4 sum-5 sum-6)
	 ((lambda perms
            (andmap (lambda (perm)
                      (equal? (perm '(a b c))
                        '((a b c) (b a c) (b c a) (a c b) (c a b) (c b a))))
              perms))
          perm-1 perm-2 perm-3 perm-4 perm-5 perm-6) 
	 )))
