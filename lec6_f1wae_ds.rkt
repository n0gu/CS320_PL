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

(define-type DeferSub
  [mtSub]
  [aSub (name symbol?) (value number?) (rest DeferSub?)])



(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list 'with (list x i) b) (with x (parse i) (parse b))]
    [(? symbol?) (id sexp)]
    [(list f a) (app f (parse a))]
    [else (error 'parse "bad syntax")]))

(define (parse-f sexp)
  (match sexp
    [(list 'deffun (list fname argname) body) (fundef fname argname (parse body))]))


; F1WAE listof-fundef listof-ds -> number
(define (interp f1wae fds ds)
  (type-case F1WAE f1wae
    [num (n) n]
    [add (l r) (+ (interp l fds ds) (interp r fds ds))]
    [sub (l r) (- (interp l fds ds) (interp r fds ds))]
    [with (x i b) (interp b fds (aSub x (interp i fds ds) ds))]
    [id (x) (lookup-x x ds)]
    [app (f a)
         (local [(define target-f (lookup-f f fds))]
           (interp (fundef-fbody target-f)
                   fds
                   (aSub (fundef-argname target-f) (interp a fds ds) (mtSub))))]))

; symbol listof-fundef -> fundef
(define (lookup-f f fds)
  (cond
    [(empty? fds) (error 'lookup-f "no function exist")]
    [else (if (symbol=? f (fundef-fname (first fds)))
              (first fds)
              (lookup-f f (rest fds)))]))

; symbol DeferSub -> number
(define (lookup-x x ds)
  (cond
    [(mtSub? ds) (error 'lookup-x "free variable ~a" x)]
    [else (if (symbol=? x (aSub-name ds))
              (aSub-value ds)
              (lookup-x x (aSub-rest ds)))]))




(define (run sexp1 fds)
  (interp (parse sexp1) fds (mtSub)))

(define functions
  (list
   (parse-f '{deffun {twice x} {+ x x}})
   (parse-f '{deffun {plus5 x} {+ x 5}})
   (parse-f '{deffun {x y} y})
   (parse-f '{deffun {+ x} x})
   (parse-f '{deffun {f x} {+ y x}})))

(run '{+ 3 {- 6 5}} functions)
(run '{with {x {+ {with {x 9} x} 2}} {with {x 4} {+ x 2}}} functions)
(run '{- {with {x 10} {twice x}} {plus5 2}} functions)
(run '{with {x 5} {x 7}} functions)
(run '{+ 3} functions)

(run '{with {y 2} {f 10}} functions)