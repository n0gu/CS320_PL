#lang plai

(define-type BMFAE
  [num (n number?)]
  [add (l BMFAE?) (r BMFAE?)]
  [sub (l BMFAE?) (r BMFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body BMFAE?)]
  [app (f BMFAE?) (a BMFAE?)]
  [newbox (v BMFAE?)]
  [setbox (b BMFAE?) (v BMFAE?)]
  [openbox (b BMFAE?)]
  [seqn (s1 BMFAE?) (s2 BMFAE?)]
  [var (id symbol?) (body BMFAE?)])

(define-type BMFAE-value
  [numV (n number?)]
  [closureV (param symbol?) (body BMFAE?) (ds DefrdSub?)]
  [boxV (address integer?)])

(define-type Value*Store
  [v*s (value BMFAE-value?) (store Store?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (addr integer?) (rest DefrdSub?)])

(define-type Store
  [mtSto]
  [aSto (addr integer?) (value BMFAE-value?) (rest Store?)])



(define (malloc st)
  (+ 1 (max-address st)))

(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (n v st)
          (max n (max-address st))]))



(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))

; symbol -> address
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free var ~a" name)]
    [aSub (x i r) (if (symbol=? x name) i (lookup name r))]))

; address -> value
(define (store-lookup addr st)
  (type-case Store st
    [mtSto () (error 'store-lookup "no store value at ~a" addr)]
    [aSto (n v rest) (if (= addr n) v (store-lookup addr rest))]))

; integer BFAE-value Store -> Store
(define (find-and-change addr new-value st)
  (type-case Store st
    [mtSto () (error 'setbox "box undefined")]
    [aSto (n v rest) (if (= addr n)
                         (aSto n new-value rest)
                         (aSto n v (find-and-change addr new-value rest)))]))


(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list 'with (list x i) b) (app (fun x (parse b)) (parse i))]
    [(list 'fun (list x) b) (fun x (parse b))]
    [(list 'newbox v) (newbox (parse v))]
    [(list 'setbox b v) (setbox (parse b) (parse v))]
    [(list 'openbox b) (openbox (parse b))]
    [(list 'seqn s1 s2) (seqn (parse s1) (parse s2))]
    [(list 'set id body) (var id (parse body))]
    [(list f a) (app (parse f) (parse a))]))


(define (interp2 bfae1 bfae2 ds st action)
  (type-case Value*Store (interp bfae1 ds st)
    [v*s (v1 s1)
         (type-case Value*Store (interp bfae2 ds s1)
           [v*s (v2 s2)
                (action v1 v2 s2)])]))
           
; BMFAE DefrdSub Store -> Value*Store(v*s)
(define (interp bfae ds st)
  (type-case BMFAE bfae
    [num (n) (v*s (numV n) st)]
    
    [add (l r) (interp2 l r ds st
                        (lambda (v1 v2 s2)
                          (v*s (num+ v1 v2)
                               s2)))]
    
    [sub (l r) (interp2 l r ds st
                        (lambda (v1 v2 s2)
                          (v*s (num- v1 v2)
                               s2)))]
    
    [id (x) (v*s (store-lookup (lookup x ds) st) st)]
    
    [fun (p b) (v*s (closureV p b ds) st)]
    
    [app (f a) (type-case BMFAE a
                 [id (x) (interp2 f a ds st
                                (lambda (v1 v2 s2)
                                    (interp (closureV-body v1)
                                            (aSub (closureV-param v1) (lookup x ds) (closureV-ds v1))
                                            s2)))]
                 [else (interp2 f a ds st
                                (lambda (v1 v2 s2)
                                  (local [(define a (malloc s2))]
                                    (interp (closureV-body v1)
                                            (aSub (closureV-param v1) a (closureV-ds v1))
                                            (aSto a v2 s2)))))])]
             
    [newbox (v) (type-case Value*Store (interp v ds st) 
                  [v*s (v s) (local [(define new-addr (malloc s))]
                               (v*s (boxV new-addr) (aSto new-addr v s)))])]
    
    [setbox (b v) (interp2 b v ds st
                           (lambda (v1 v2 s2)
                             (v*s v2 (find-and-change (boxV-address v1) v2 s2))))]
    
    [openbox (b) (type-case Value*Store (interp b ds st)
                   [v*s (v s) (v*s (store-lookup (boxV-address v) s) s)])]
    
    [seqn (s1 s2) (interp2 s1 s2 ds st
                           (lambda (v1 v2 s2)
                             (v*s v2 s2)))]
    
    [var (id body) (local [(define addr (lookup id ds))]
                     (type-case Value*Store (interp body ds st)
                       [v*s (v s) (v*s v (aSto addr v s))]))]))
                                                        



(define (run sexp)
  (interp (parse sexp) (mtSub) (mtSto)))


(run '{newbox 8})
(run '{with {b {newbox 0}} {setbox b 10}})
(run '{with {b {newbox 0}} {seqn {setbox b 10}
                                 {openbox b}}})
(run '{with {q {newbox 10}}
  {setbox {seqn {setbox q 12} q}
          {openbox q}}})
(run '{with {b {newbox 8}} {seqn {setbox b 10} {+ 4 {openbox b}}}})

; new cases with set, call-by-reference
(run '{with {x 5} {set x 16}})
(run '{with {swap {fun {x} {fun {y} {with {z {newbox {openbox y}}} {seqn {setbox y {openbox x}} {setbox x {openbox z}}}}}}}
       {with {x {newbox 10}} {with {y {newbox 20}} {seqn {{swap x} y} {openbox x}}}}})
(run '{with {swap {fun {x} {fun {y} {with {z {{fun {t} t} y}}
                                    {seqn {set y x} {set x z}}}}}}
      {with {a 10} (with {b 20} {seqn {{swap a} b} a})}})