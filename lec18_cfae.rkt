#lang plai
;; lecture 18 - compiled FAE

(define-type FAE
  [num (n number?)]
  [add (l FAE?) (r FAE?)]
  [sub (l FAE?) (r FAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body FAE?)]
  [app (f FAE?) (a FAE?)])

(define-type CFAE
  [cnum (n number?)]
  [cadd (l CFAE?) (r CFAE?)]
  [csub (l CFAE?) (r CFAE?)]
  [cid (pos number?)]
  [cfun (body CFAE?)]
  [capp (f CFAE?) (a CFAE?)])

(define-type CFAE-value
  [numV (n number?)]
  [closureV (body CFAE?) (ds (listof CFAE-value?))])

(define-type CFAE-cont
  [mtK]
  [addSecondK (r CFAE?) (ds list?) (k CFAE-cont?)]
  [doAddK (v CFAE-value?) (k CFAE-cont?)]
  [subSecondK (r CFAE?) (ds list?) (k CFAE-cont?)]
  [doSubK (v CFAE-value?) (k CFAE-cont?)]
  [appArgK (arg CFAE?) (ds list?) (k CFAE-cont?)]
  [doAppK (v CFAE-value?) (k CFAE-cont?)])

(define-type CDefrdSub
  [mtCSub]
  [aCSub (name symbol?) (rest CDefrdSub?)])

(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))

(define (compile fae cds)
  (type-case FAE fae
    [num (n) (cnum n)]
    [add (l r) (cadd (compile l cds) (compile r cds))]
    [sub (l r) (csub (compile l cds) (compile r cds))]
    [id (name) (cid (locate name cds))]
    [fun (param body) (cfun (compile body (aCSub param cds)))]
    [app (f a) (capp (compile f cds) (compile a cds))]))

(define (locate name ds)
  (type-case CDefrdSub ds
    [mtCSub () (error 'locate "free variable")]
    [aCSub (p rest) (if (symbol=? name p)
                        0
                        (+ 1 (locate name rest)))]))
           
(define cfae-reg (cnum 0))
(define k-reg (mtK))
(define v-reg (numV 0))
(define ds-reg empty)
           
(define (interp) ; ds is a list now
  (type-case CFAE cfae-reg
    [cnum (n) (begin
                (set! v-reg (numV n))
                (continue))]
    [cadd (l r) (begin
                  (set! cfae-reg l)
                  (set! k-reg (addSecondK r ds-reg k-reg))
                  (interp))]
    [csub (l r) (begin
                  (set! cfae-reg l)
                  (set! k-reg (subSecondK r ds-reg k-reg))
                  (interp))]
    [cid (pos) (begin
                 (set! v-reg (list-ref ds-reg pos))
                 (continue))]
    [cfun (body) (begin
                   (set! v-reg (closureV body ds-reg))
                   (continue))]
    [capp (f a) (begin
                  (set! cfae-reg f)
                  (set! k-reg (appArgK a ds-reg k-reg))
                  (interp))]))

(define (continue)
  (type-case CFAE-cont k-reg
    [mtK () v-reg]
    [addSecondK (r ds k) (begin
                           (set! cfae-reg r)
                           (set! ds-reg ds)
                           (set! k-reg (doAddK v-reg k))
                           (interp))]
    [doAddK (first-v k) (begin
                          (set! v-reg (num+ first-v v-reg))
                          (set! k-reg k)
                          (continue))]
    [subSecondK (r ds k) (begin
                           (set! cfae-reg r)
                           (set! ds-reg ds)
                           (set! k-reg (doSubK v-reg k))
                           (interp))]
    [doSubK (first-v k) (begin
                          (set! v-reg (num- first-v v-reg))
                          (set! k-reg k)
                          (continue))]
    [appArgK (a ds k) (begin
                        (set! cfae-reg a)
                        (set! ds-reg ds)
                        (set! k-reg (doAppK v-reg k))
                        (interp))]
    [doAppK (fun-v k) (begin
                        (set! cfae-reg (closureV-body fun-v))
                        (set! ds-reg (cons v-reg (closureV-ds fun-v)))
                        (set! k-reg k)
                        (interp))]))
                       

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
       [else (app (parse-sexpr (first sexp))
                  (parse-sexpr (second sexp)))])]))


(define (run sexp)
  (begin
    (set! ds-reg empty)
    (set! k-reg (mtK))
    (set! cfae-reg (compile (parse-sexpr sexp) (mtCSub)))
    (set! v-reg (numV 0))
    (interp)))

(test (run '10) (numV 10))
(test (run '{+ 10 7}) (numV 17))
(test (run '{- 10 7}) (numV 3))
(test (run '{{fun {x} {+ x 12}} {+ 1 17}}) (numV 30))
(test (run '{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}}{fun {y} {+ x y}}}} 0}) (numV 3))
(compile (parse-sexpr '{{{fun {x} {fun {y} {+ y x}}} 3} 4}) (mtCSub))