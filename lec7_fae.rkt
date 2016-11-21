#lang plai


(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))


(define-type FAE
  [num (n number?)]
  [add (l FAE?) (r FAE?)]
  [sub (l FAE?) (r FAE?)]
  [id (name symbol?)]
; [with (name symbol?) (value FWAE?) (body FWAE?)] (no more with)
  [fun (param symbol?) (body FAE?)]
  [app (f FAE?) (a FAE?)])

(define-type FAE-value
  [numV (n number?)]
  [closureV (param symbol?) (body FAE?) (ds DefrdSub?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FAE-value?) (rest DefrdSub?)])



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
(define (interp fae ds)
  (type-case FAE fae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (x) (lookup-x x ds)]
;   [with (x i b) (interp (subst b x (interp i ds)) ds)] 
    [fun (p b) (closureV p b ds)]
    [app (f a) (local [(define ftn (interp f ds))] ; ftn is closureV.
                 (interp (closureV-body ftn)
                         (aSub (closureV-param ftn) (interp a ds) (closureV-ds ftn))))]))
        
(define (lookup-x name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free var ~a" name)]
    [aSub (x i r) (if (symbol=? x name) i (lookup-x name r))]))


; subst :: method that doesn't use DefrdSub
; FWAE symbol FWAE -> FWAE
(define (subst body x val)
  (type-case FAE body
    [num (n) body]
    [add (l r) (add (subst l x val) (subst r x val))]
    [sub (l r) (sub (subst l x val) (subst r x val))]
    [id (y) (if (symbol=? x y) val body)]
;   [with (y i b) (with y
;                       (subst i x val)
;                       (if (symbol=? x y) b (subst b x val)))]
    [fun (p b) (if (symbol=? x p) body (fun p (subst b x val)))]
    [app (f a) (app (subst f x val) (subst a x val))]))



(define (run sexp)
  (interp (parse sexp) (mtSub)))

(run '{{fun {x} {+ x 1}} 10})
(run '{with {x {with {x 3} {- 5 x}}} {+ 1 x}})
(run '{with {f {fun {x} {+ x x}}} {- 20 {f 10}}})
(run '{- 20 {{fun {x} {+ x x}} 17}})
(run '{fun {x} {+ 1 x}})

; beware of this case
(run '{with {y 2} {{fun {x} {+ y x}} 8}})
(run '{{with {y 2} {fun {x} {+ y x}}} 8})
(run '{with {scope_test {fun {x} {+ y x}}} {with {y 2} {scope_test 8}}})
