#lang plai

(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n (strict x)) (numV-n (strict y))))))
(define num+ (num-op +))
(define num- (num-op -))

; LFAE-value -> LFAE-value
(define (strict l-val)
  (type-case LFAE-value l-val
    [exprV (expr ds val) (if (not (unbox val))
                             (local [(define v (strict (interp expr ds)))]
                               (begin (set-box! val v) v))
                             (unbox val))]
    [else l-val]))

(define-type LFAE
  [num (n number?)]
  [add (l LFAE?) (r LFAE?)]
  [sub (l LFAE?) (r LFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body LFAE?)]
  [app (f LFAE?) (a LFAE?)])

(define-type LFAE-value
  [numV (n number?)]
  [closureV (param symbol?) (body LFAE?) (ds DefrdSub?)]
  [exprV (expr LFAE?) (ds DefrdSub?) (value (box/c (or/c false LFAE-value?)))])
  
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value LFAE-value?) (rest DefrdSub?)])



(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list 'with (list x i) b) (app (fun x (parse b)) (parse i))] ; no more with
    [(list 'fun (list x) b) (fun x (parse b))]
    [(list f a) (app (parse f) (parse a))]))


; FAE -> FAE-value
(define (interp lfae ds)
  (type-case LFAE lfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (x) (lookup-x x ds)]
    [fun (p b) (closureV p b ds)]
    [app (f a) (local [(define ftn (strict (interp f ds)))] ; ftn is closureV.
                 (interp (closureV-body ftn)
                         (aSub (closureV-param ftn) (exprV a ds (box #f)) (closureV-ds ftn))))]))
        
(define (lookup-x name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free var ~a" name)]
    [aSub (x i r) (if (symbol=? x name) i (lookup-x name r))]))



(define (run sexp)
  (interp (parse sexp) (mtSub)))

(run '{{fun {x} {+ x 1}} 10})
(run '{with {x {with {x 3} {- 5 x}}} {+ 1 x}})
(run '{with {f {fun {x} {+ x x}}} {- 20 {f 10}}})
(run '{- 20 {{fun {x} {+ x x}} 17}})
(run '{fun {x} {+ 1 x}})
(run '{with {x 15} {{fun {f} {+ f f}} x}})

; beware of this case
(run '{with {y 2} {{fun {x} {+ y x}} 8}})
(run '{{with {y 2} {fun {x} {+ y x}}} 8})
(run '{{fun {f} {f 1}} {fun {x} {+ x 1}}})
(run '{{fun {x} {+ {+ x x} {+ x x}}}{- {+ 4 5} {+ 8 9}}})
(run '{{fun {x} x} 8})
; lazy
(run '{{fun {x} 0} {+ 1 {fun {y} 2}}})