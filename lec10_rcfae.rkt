#lang plai

(define-type RCFAE
  [num (n number?)]
  [add (l RCFAE?) (r RCFAE?)]
  [sub (l RCFAE?) (r RCFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body RCFAE?)]
  [app (fun RCFAE?) (arg RCFAE?)]
  [if0 (cond RCFAE?) (t-act RCFAE?) (f-act RCFAE?)]
  [rec (name symbol?) (body RCFAE?) (expr RCFAE?)])

(define-type RCFAE-value
  [numV (n number?)]
  [closureV (param symbol?) (body RCFAE?) (ds DefrdSub?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value RCFAE-value?) (rest DefrdSub?)]
  [aRecSub (name symbol?) (addr (box/c RCFAE-value?)) (rest DefrdSub?)])


; numV numV -> numV
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))

; symbol ds -> RCFAE-value
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable ~a" name)]
    [aSub (n v r) (if (symbol=? n name) v (lookup name r))]
    [aRecSub (n a r) (if (symbol=? n name) (unbox a) (lookup name r))]))
                               

; RCFAE-value (especially numV) -> boolean
(define (iszero? val)
  (zero? (numV-n val)))



; sexp -> RCFAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list 'with (list x i) b) (app (fun x (parse b)) (parse i))]
    [(list 'fun (list p) b) (fun p (parse b))]
    [(list f a) (app (parse f) (parse a))]
    [(list 'if0 c t f) (if0 (parse c) (parse t) (parse f))]
    [(list 'rec (list n b) e) (rec n (parse b) (parse e))]))



; RCFAE -> RCFAE-value, fac: dummy value version
(define (interp rcfae ds)
  (type-case RCFAE rcfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (x) (lookup x ds)]
    [fun (p b) (closureV p b ds)]
    [app (f a) (local [(define ftn (interp f ds))]
                 (interp (closureV-body ftn)
                         (aSub (closureV-param ftn) (interp a ds) (closureV-ds ftn))))]
    [if0 (c t f) (if (iszero? (interp c ds)) (interp t ds) (interp f ds))]
    [rec (n b e) (local [(define value-holder (box (numV 0)))
                         (define new-ds (aRecSub n value-holder ds))]
                   (begin
                     (set-box! value-holder (interp b new-ds))
                     (interp e new-ds)))]))
                   
                   
(define (run sexp)
  (interp (parse sexp) (mtSub)))

(run '{rec {count {fun {n} {if0 n 0 {+ 1 {count {- n 1}}}}}}
        {count 8}})