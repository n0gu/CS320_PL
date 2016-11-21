#lang plai
;; lecture 16 - kcfae with fun, app, if0 and withcc

(define-type KCFAE
  [num (n number?)]
  [add (l KCFAE?) (r KCFAE?)]
  [sub (l KCFAE?) (r KCFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body KCFAE?)]
  [app (f KCFAE?) (a KCFAE?)]
  [if0 (test-expr KCFAE?) (then-expr KCFAE?) (else-expr KCFAE?)]
  [withcc (id symbol?) (body KCFAE?)])
  
(define-type KCFAE-value
  [numV (n number?)]
  [closureV (param symbol?) (body KCFAE?) (ds DefrdSub?)]
  [contV (cont procedure?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value KCFAE-value?) (rest DefrdSub?)])

(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))

(define (lookup target-name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (name val rest) (if (equal? name target-name)
                              val
                              (lookup target-name rest))]))

(define (numzero? kcfae-val)
  (= 0 (numV-n kcfae-val)))

(define (interp kcfae ds k)
  (type-case KCFAE kcfae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                    (lambda (v1)
                      (interp r ds
                              (lambda (v2)
                                (k (num+ v1 v2))))))]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num- v1 v1))))))]
    [id (name) (k (lookup name ds))]
    [fun (param body) (k (closureV param body ds))]
    [app (f a) (interp f ds
                       (lambda (f-val)
                         (interp a ds
                                 (lambda (a-val)
                                   (type-case KCFAE-value f-val
                                     [closureV (p b closure-ds)
                                               (interp b (aSub p a-val closure-ds) k)]
                                     [contV (c) (c a-val)]
                                     [else (error)])))))]
    [if0 (test then else) (interp test ds
                                  (lambda (t-val)
                                    (if (numzero? t-val)
                                        (interp then ds k)
                                        (interp else ds k))))]
    [withcc (id body) (interp body 
                              (aSub id
                                    (contV k) ds)
                              k)]))

(define (parse-sexpr sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse-sexpr (second sexp))
                 (parse-sexpr (third sexp)))]
       [(-) (sub (parse-sexpr (second sexp))
                 (parse-sexpr (third sexp)))]
       [(fun) (fun (first (second sexp))
                   (parse-sexpr (third sexp)))]
       [(if0) (if0 (parse-sexpr (second sexp))
                   (parse-sexpr (third sexp))
                   (parse-sexpr (fourth sexp)))]
       [(withcc) (withcc (second sexp)
                         (parse-sexpr (third sexp)))]
       [else (app (parse-sexpr (first sexp))
                  (parse-sexpr (second sexp)))])]))

(define (run sexp)
  (interp (parse-sexpr sexp) (mtSub) (lambda (x) x)))


(run '{withcc k {+ 1 {k 2}}})
(run '{withcc done {{withcc esc
                            {done {+ 1 {withcc k
                                               {esc k}}}}}
                    3}})
                                           