
(define empty?
  (lambda (lst)
    (if (eq? lst '())
        #t
        #f)))

(define fold-left
  (lambda (fun acc lst)
    (if (empty? lst )
        acc
        (fold-left fun (fun acc (car lst) )  (cdr lst)))))


(define fold-right
  (lambda (fun acc lst)
    (if (empty? lst )
        acc
       (fun (car lst) (fold-right fun acc (cdr lst))))))


(define cons*
  (lambda lst
    (fold-left cons (car lst) (cdr lst) )))


(define length
  (lambda (lst)
    (if (eq? (cdr lst) '())
        1
        (+ 1 (length (cdr lst))))))


(define append
  (lambda (lst1 lst2)
    (cons lst1 lst2)))

(define map
  (lambda (fun lst)
    (if (eq? (cdr lst) '())
        (append (fun (car lst)) '())
        (append (fun (car lst)) (map fun (cdr lst))))))

(define list?
  (lambda (x)
    (or (null? x)
        (and (pair? x)
             (list? (cdr x))))))		

(define not
  (lambda (x) (if x #f #t)))

(define list (lambda x x))

(define zero? 
    (lambda (x) (= x 0)))

(define integer?
    (lambda (x)
      (and (rational? x) (= (denominator x) 1))))

(define number?
    (lambda (x)
      (or (flonum? x) (rational? x))))


(define gcd
  (let ((gcd gcd) (null? null?)
	(car car) (cdr cdr))
    (letrec ((gcd-loop
	      (lambda (x ys)
		(if (null? ys)
		    x
		    (gcd-loop (gcd x (car ys)) (cdr ys))))))
      (lambda x
	(if (null? x)
	    0
	    (gcd-loop (car x) (cdr x)))))))




(let ((flonum? flonum?) (rational? rational?)
      (exact->inexact exact->inexact)
      (fold-left fold-left) (map map)
      (_+ +) (_* *) (_/ /) (_= =) (_< <)
      (car car) (cdr cdr) (null? null?))
  (let ((^numeric-op-dispatcher
	 (lambda (op)
	   (lambda (x y)
	     (cond
	      ((and (flonum? x) (rational? y)) (op x (exact->inexact y)))
	      ((and (rational? x) (flonum? y)) (op (exact->inexact x) y))
	      (else (op x y)))
		  ))))
      (set! + (lambda x (fold-left (^numeric-op-dispatcher _+) 0 x)))
      (set! * (lambda x (fold-left (^numeric-op-dispatcher _*) 1 x)))
      (set! / (let ((/ (^numeric-op-dispatcher _/)))
		(lambda (x . y)
		  (if (null? y)
		      (/ 1 x)
		      (fold-left / x y)))))
    (let ((^comparator
	   (lambda (op)
	     (letrec ((comparator
		       (lambda (x ys)
			 (or (null? ys)
			     (and (op x (car ys))
				  (comparator (car ys) (cdr ys)))))))
	       (lambda (x . y)
		 (comparator x y))))))
      (set! = (^comparator (^numeric-op-dispatcher _=)))
      (set! < (^comparator (^numeric-op-dispatcher _<))))))


 (define -
  (lambda (x . y)
    (if (empty? y)
        x
        (+ x (minus y)))))

(define minus
  (lambda (lst)
    (if (empty? (cdr lst))
        (* -1 (car lst))
        (+ (* -1 (car lst)) (minus (cdr lst))))))
    
(define >
  (let ((null? null?) (not not)
        (car car) (cdr cdr)
        (< <) (= =))
    (letrec ((>-loop
	      (lambda (x ys)
	        (or (null? ys)
		    (and (not (< x (car ys))) (not (= x (car ys)))
		         (>-loop (car ys) (cdr ys)))))))
      (lambda (x . y)
        (>-loop x y)))))

(define equal?
  (let ((= =) (string->list string->list)
	(rational? rational?) (flonum? flonum?)
	(pair? pair?) (char? char?)
	(string? string?) (eq? eq?)
	(car car) (cdr cdr)
	(char->integer char->integer))
    (letrec ((equal?-loop
	      (lambda (x y)
		(cond
		 ((and (rational? x) (rational? y)) (= x y))
		 ((and (flonum? x) (flonum? y)) (= x y))
		 ((and (char? x) (char? y)) (= (char->integer x) (char->integer y)))
		 ((and (pair? x) (pair? y))
		  (and (equal?-loop (car x) (car y)) (equal?-loop (cdr x) (cdr y))))
		 ((and (string? x) (string? y)) (equal?-loop (string->list x) (string->list y)))
		 (else (eq? x y))))))
    equal?-loop)))

(define string->list
  (let ((string-ref string-ref)
	(string-length string-length)
	(< <) (- -) (cons cons))
    (lambda (s)
      (letrec
	  ((s->l-loop
	    (lambda (n a)
	      (if (< n 0)
		  a
		  (s->l-loop (- n 1) (cons (string-ref s n) a))))))
	(s->l-loop (- (string-length s) 1) '())))))


  (define make-string
  (let ((null? null?) (car car)
	(make-string make-string))
    (lambda (x . y)
      (if (null? y)
	  (make-string x #\nul)
	  (make-string x (car y))))))