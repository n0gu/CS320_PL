#lang plai

(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (id symbol?) (value WAE?) (body WAE?)]
  [id (name symbol?)])

(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list 'with (list x i) b) (with x (parse i) (parse b))]
    [(? symbol?) (id sexp)]))

; WAE -> number
(define (interp wae)
  (type-case WAE wae
    [num (n) n]
    [add (l r) (+ (interp l) (interp r))]
    [sub (l r) (- (interp l) (interp r))]
    [with (x i b) (interp (subst b x (interp i)))]
    [id (x) (error "free identifier")]))

; WAE -> WAE
(define (subst body name value)
  (type-case WAE body
    [num (n) body]
    [add (l r) (add (subst l name value) (subst r name value))]
    [sub (l r) (sub (subst l name value) (subst r name value))]
    [with (x i b) (with x 
                         (subst i name value)
                         (if (symbol=? name x)
                             b
                             (subst b name value)))]
    [id (x) (if (symbol=? name x) (num value) body)]))
                 
(define (run sexp)
  (interp (parse sexp)))

(run '{+ 3 {- 6 5}})
(run '{with {x {+ {with {x 9} x} 2}} {with {x 4} {+ x 2}}})
