(define (nullo s)
  (== s '()))

(define (conso a d s)
  (== (cons a d) s))

(define (appendo l s out)
  (conde
    [(== l '()) (== s out)]
    [(fresh (a d res)
       (== `(,a . ,d) l)
       (== `(,a . ,res) out)
       (appendo d s res))]))

(define (membero a s)
  (conde
   [(== s '()) fail]
   [(fresh (d)
	   (== (cons a d) s))]
   [(fresh (a0 d)
	   (== (cons a0 d) s)
	   (membero a d))]))
	    
(define (assoco a s out)
  (conde
   [(== s '()) fail]
   [(fresh (d0 d1)
	   (== (cons `(,a . ,d0) d1) s)
	   (== `(,a . ,d0) out))]
   [(fresh (a0 d0 d1)
	   (== (cons `(,a0 . ,d0) d1) s)
	   (assoco a d1 out))]))

(define rembero
  (lambda (x ls out)
    (conde
      ((== '() ls) (== '() out))
      ((fresh (a d res)
         (== `(,a . ,d) ls)
         (rembero x d res)
         (conde
           ((== a x) (== out res))
           ((=/= a x) (== `(,a . ,res) out))))))))

(define (sublisto s0 s1)
  (conde
   [(== s0 '())]
   [(fresh (a d0 d1)
	   (conso a d0 s0)
	   (conso a d1 s1)
	   (sublisto d0 d1))]
   [(fresh (a0 a1 d0 d1)
	   (=/= a0 a1)
	   (conso a0 d0 s0)
	   (conso a1 d1 s1)
	   (sublisto s0 d1))]))

(define (mapo f)
  (lambda (s)
    (conde [(== s '())]
	   [(fresh (a d)
		   (conso a d s)
		   (f a)
		   ((mapo f) d))])))

(define (mapo2 f)
  (lambda (s0 s1)
    (conde [(== s0 '()) (== s1 '())]
	   [(fresh (a0 a1 d0 d1)
		   (conso a0 d0 s0)
		   (conso a1 d1 s1)
		   (f a0 a1)
		   ((mapo2 f) d0 d1))])))

(define (filtero f)
  (lambda (ls out)
    (conde
      ((== '() ls) (== '() out))
      ((fresh (a d res)
         (== `(,a . ,d) ls)
         ((filtero f) d res)
	 (conda
	  ((f a) (== `(,a . ,res) out))
	  ((== out res))))))))


(define (filtero-inv f)
  (lambda (ls out)
    (conde
      ((== '() ls) (== '() out))
      ((fresh (a d res)
         (== `(,a . ,d) ls)
         ((filtero-inv f) d res)
	 (conda
	  ((f a) (== out res))
	  ((== `(,a . ,res) out))))))))
	 
