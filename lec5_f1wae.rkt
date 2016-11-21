#lang plai

(define-type F1WAE
  [num (n number?)]
  [add (l F1WAE?) (r F1WAE?)]
  [sub (l F1WAE?) (r F1WAE?)]
  [with (name symbol?) (value F1WAE?) (body F1WAE?)]
  [id (name symbol?)]
  [app (fname symbol?) (arg F1WAE?)])

(define-type FunDef
  [fundef (fname symbol?) (argname symbol?) (fbody F1WAE?)])



; sexp -> FunDef
(define (parse-f sexp)
  (match sexp
    [(list 'deffun (list fname argname) body) (fundef fname argname (parse body))]))

; sexp -> F1WAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list 'with (list x i) b) (with x (parse i) (parse b))]
    [(? symbol?) (id sexp)]
    [(list f a) (app f (parse a))]
    [else (error 'parse "bad syntax")]))




; F1WAE list-of-fundef -> number
(define (interp f1wae fds)
  (type-case F1WAE f1wae
    [num (n) n]
    [add (l r) (+ (interp l fds) (interp r fds))]
    [sub (l r) (- (interp l fds) (interp r fds))]
    [with (x i b) (interp (subst b x (interp i fds)) fds)]
    [id (x) (error 'interp "free variable ~a" x)]
    [app (f a)
         (local [(define target-f (lookup f fds))]
           (interp (subst (fundef-fbody target-f) (fundef-argname target-f) (interp a fds))
                   fds))]))
    



; F1WAE symbol number -> WAE
(define (subst body name value)
  (type-case F1WAE body
    [num (n) body]
    [add (l r) (add (subst l name value) (subst r name value))]
    [sub (l r) (sub (subst l name value) (subst r name value))]
    [with (x i b) (with x
                        (subst i name value)
                        (if (symbol=? x name)
                            b
                            (subst b name value)))]
    [id (x) (if (symbol=? x name) (num value) body)]
    [app (f a) (app f (subst a name value))]))



; symbol list-of-fundefs -> fundef
(define (lookup f fds)
  (cond
    [(empty? fds) (error 'lookup "no function exist")]
    [else (if (symbol=? f (fundef-fname (first fds)))
              (first fds)
              (lookup f (rest fds)))]))
                        
  
  
  
(define (run sexp1 fds)
  (interp (parse sexp1) fds))

(define functions
  (list
   (parse-f '{deffun {twice x} {+ x x}})
   (parse-f '{deffun {plus5 x} {+ x 5}})
   (parse-f '{deffun {x y} y})
   (parse-f '{deffun {+ x} x})
   (parse-f '{deffun {f f} f})
   (parse-f '{deffun {scopetest x} {+ y x}})))

(run '{+ 3 {- 6 5}} functions)
(run '{with {x {+ {with {x 9} x} 2}} {with {x 4} {+ x 2}}} functions)
(run '{- {with {x 10} {twice x}} {plus5 2}} functions)
(run '{with {x 5} {x 7}} functions)
(run '{+ 3} functions)
(run '{f 5} functions)
(run '{with {y 2} {scopetest 10}} functions)