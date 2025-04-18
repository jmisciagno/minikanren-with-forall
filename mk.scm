;; Jason Hemann and Dan Friedman
;; microKanren, final implementation from paper
;; Edited by John Misciagno in 2025

(define (var x) (vector x))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (var? x1) (var? x2) (= (vector-ref x1 0) (vector-ref x2 0))))

(define (var<? x1 x2) (< (vector-ref x1 0) (vector-ref x2 0)))
(define (var-u x) (vector x 'U)) ; tag var as universally quantified
(define (var-u? x) (and (vector? x) (> (vector-length x) 1) (eq? (vector-ref x 1) 'U)))

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

(define (walk-pair x s)
  (let ((res (walk x s)))
      (cons x res)))

(define (vars g)
  (lambda (s/c)
    (map car (take-all (g s/c)))))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v)
         (or
           (occurs-check x (car v) s)
           (occurs-check x (cdr v) s)))
        (else #f)))))

(define ext-s-check
  (lambda (x v s)
    (cond
      ((occurs-check x v s) #f)
      (else (cons `(,x . ,v) s)))))

(define (== u v)
  (lambda (s/c)
    (let ((s (unify u v (car s/c))))
      (if s (unit `(,s . ,(cdr s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (_and a b) (and a b))
(define (_or a b) (or a b))

(define (fact-equal? f0 f1)
  (and (equal? (car f0) (car f1))
       (or (and (equal? (cdr f0) (cdr f1)))
	   (and (var? (cdr f0)) (not (var-u? (cdr f0))))
	   (and (var? (cdr f1)) (not (var-u? (cdr f1)))))))

(define (flip p) (cons (cdr p) (car p)))

(define (fact-member f fs)
  (or (equal? fs (unify (car f) (cdr f) fs)) ; check for added information
      (fold-left _or
		 #f
		 (map (lambda (f0)
			(or (fact-equal? f f0)
			    (fact-equal? f (flip f0))
			    (fact-equal? (flip f) f0)
			    (fact-equal? (flip f) (flip f0))))
		      fs))))

(define (fact-in-worlds? f ws)
  (fold-left _or
	     #f
	     (map (lambda (w) (fact-member f (car w))) ws)))
  
(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
     ((and (var? u) (var? v) (var=? u v)) s)
     ((var? u) (ext-s-check u v s))
     ((and (var? u) (var? v) (var<? v u)) (ext-s-check v u s)) ; normalize var order
     ((var? v) (ext-s-check v u s))
     ((and (pair? u) (pair? v))
      (let ((s (unify (car u) (car v) s)))
        (and s (unify (cdr u) (cdr v) s))))
     (else (and (eqv? u v) s)))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (cdr s/c)))
      ((f (var c)) `(,(car s/c) . ,(+ c 1))))))

(define (call/fresh-u f)
  (lambda (s/c)
    (let ((c (cdr s/c)))
      ((f (var-u c)) `(,(car s/c) . ,(+ c 1))))))

; should fail if first var is var-u? and 
; second var is either not a var?, is a var-u?, var<? first var
(define (bound-to u v) (or (not (var? u))
			   (and (var-u? u) (not (var=? u v)))
			   (var<? u v)))


(define (call/forall f)
  (lambda (s/c)
    (let ((c (cdr s/c)))
	(let ((res (take-all ((call/fresh-u f) s/c))))
	  (filter (lambda (s)
		    (not (or (cond ((walk-pair (var-u c) (car s)) =>
				    (lambda (p)
				      (bound-to (cdr p) (car p))))
				   (else #f))
			     (cond ((walk-pair (var-u c) (map flip (car s))) =>
				    (lambda (p)
				      (bound-to (cdr p) (car p))))
				   (else #f)))))
		  res)))))

(define (_conj g1 g2)
  (lambda (s/c)
    (bind (g1 s/c) g2)))

; disj with unique variables accross possible worlds
(define (_disj g1 g2) 
  (lambda (s/c)
    (let* ((g1-s/c (g1 s/c))
	   (c (get-c g1-s/c)))
      (mplus g1-s/c (g2 (+c s/c c))))))

(define (get-c x)
  (cond ((null? x) 0)
	((procedure? x) (get-c (x)))
	((pair? x) (+ (cdr (car x)) (get-c (cdr x))))
	(else x)))

(define (+c s/c n)
  (cons (car s/c) (+ (cdr s/c) n)))

(define (remove-universal-aux2 s)
  (filter (lambda (p)
	    (and (not (var-u? (car p))) (not (var-u? (cdr p)))))
	  s))
  
(define (remove-universal-aux s)
  (map (lambda (w)
	 (cons (remove-universal-aux2 (car w)) (cdr w)))
       s))

(define (remove-universal g)
  (lambda (s/c)
    (remove-universal-aux (take-all (g s/c)))))

(define (log x) (begin (displayln x) x))
(define (id x) x)

(define (fix x) (if (eq? x #f) '(#f) x))

(define (implies g1 g2)
  (lambda (s/c)
    (let ((g1-res (take-all (g1 s/c))))
      (let ((g2-res (take-all (g2 s/c))))
      ((fold-left _conj
		  succeed
		  (map (lambda (x)
			 (let ((t (take-all (bind (unit x) g2))))
			   (if (null? t)
			       fail
			       (if (fold-left _and #t
					      (id (fix (fold-left _or
							 #f
							 (map (lambda (x0) (map (lambda (x1) (fact-in-worlds? x1 g1-res)) (car x0))) g2-res)))))
				     (remove-universal (_conj g1 g2))
				     fail))))
		       g1-res)) s/c)))))


(define (mplus $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    (else (cons (car $1) (mplus (cdr $1) $2)))))

(define (bind $ g)
  (cond
    ((null? $) mzero)
    ((procedure? $) (lambda () (bind ($) g)))
    (else (mplus (g (car $)) (bind (cdr $) g)))))

;;;; How to make a simple miniKanren (substitution only)

(define-syntax Zzz
  (syntax-rules ()
    ((_ g) (lambda (s/c) (lambda () (g s/c))))))

(define-syntax conj
  (syntax-rules ()
    ((_ g) (Zzz g))
    ((_ g0 g ...) (_conj (Zzz g0) (conj g ...)))))

(define-syntax disj
  (syntax-rules ()
    ((_ g) (Zzz g))
    ((_ g0 g ...) (_disj (Zzz g0) (disj g ...)))))

(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g ...) (conj g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/fresh
      (lambda (x0)
        (fresh (x ...) g0 g ...))))))

(define-syntax forall
  (syntax-rules ()
    ((_ () g0 g ...) (conj g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/forall
      (lambda (x0)
        (forall (x ...) g0 g ...))))))
	  
(define-syntax exists
  (syntax-rules ()
    ((exists (v ...) g0 g ...)
     (fresh (v ...) g0 g ...))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) ...) (disj (conj g0 g ...) ...))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x ...) g0 g ...)
     (map reify-1st (take n (call/goal (fresh (x ...) g0 g ...)))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (map reify-1st (take-all (call/goal (fresh (x ...) g0 g ...)))))))

(define empty-state '(() . 0))

(define (call/goal g) (g empty-state))

(define (pull $)
  (if (procedure? $) (pull ($)) $))

(define (take-all $)
  (let (($ (pull $)))
    (if (null? $) '() (cons (car $) (take-all (cdr $))))))

(define (take n $)
  (if (zero? n) '()
    (let (($ (pull $)))
      (if (null? $) '() (cons (car $) (take (- n 1) (cdr $)))))))

(define (reify-1st s/c)
  (let ((v (walk* (var 0) (car s/c))))
    (walk* v (reify-s v '()))))

(define (walk* v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) v)
      ((pair? v) (cons (walk* (car v) s)
                   (walk* (cdr v) s)))
      (else  v))))

(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
      ((var? v)
       (let  ((n (reify-name (length s))))
         (cons `(,v . ,n) s)))
      ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
      (else s))))

(define (reify-name n)
  (string->symbol
    (string-append "_" "." (number->string n))))

(define succeed (== #f #f))
(define fail (== #f #t))
