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
	
