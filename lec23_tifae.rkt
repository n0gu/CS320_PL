#lang plai-typed

; lecture 23 - type inference fae

(define-type TIFAE
  [num (n : number)]
  [add (l : TIFAE) (r : TIFAE)]
  [sub (l : TIFAE) (r : TIFAE)]
  [id (x : symbol)]
  [fun (param : symbol)
       (paramty : TE)
       (body : TIFAE)]
  [app (fun-expr : TIFAE) (arg-expr : TIFAE)]
;  [pair (fst-expr : TIFAE) (snd-expr : TIFAE)]
;  [fst (pair-expr : TIFAE)]
;  [snd (pair-expr : TIFAE)])
  [withtype (tyid : symbol)
            (var1-name : symbol) (var1-ty : TE)
            (var2-name : symbol) (var2-ty : TE)
            (body-expr : TIFAE)]
  [cases (name : symbol) (dispatch-expr : TIFAE)
    (var1-name : symbol) (bind1-name : symbol) (var1-body : TIFAE)
    (var2-name : symbol) (bind2-name : symbol) (var2-body : TIFAE)])

(define-type TIFAE-value
  [numV (n : number)]
;  [boolV (b : boolean)]
  [closureV (param : symbol) (body : TIFAE) (ds : DefrdSub)]
;  [pairV (left : TIFAE-value) (right : TIFAE-value)]
  [variantV (right? : boolean) (value : TIFAE-value)]
  [constructV (right? : boolean)])

(define-type TE
  [numTE]
;  [boolTE]
  [arrowTE (arg : TE) (result : TE)]
;  [crossTE (f : TE) (s : TE)]
  [guessTE]
  [idTE (name : symbol)])

(define-type T
  [numT]
;  [boolT]
  [arrowT (arg : T) (result : T)]
;  [crossT (f : T) (s : T)]
  [varT (is : (boxof (Option T)))]
  [idT (name : symbol)])

(define-type (Option 'alpha)
  [none]
  [some (v : 'alpha)])

(define (parse-te te)
  (type-case TE te
    [numTE () (numT)]
;    [boolTE () (boolT)]
    [arrowTE (arg result) (arrowT (parse-te arg) (parse-te result))]
;    [crossTE (f s) (crossT (parse-te f) (parse-te s))]
    [guessTE () (varT (box (none)))]
    [idTE(name) (idT name)]))

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol) (value : TIFAE-value) (rest : DefrdSub)])

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest) (if (symbol=? name sub-name)
                                  val
                                  (lookup name rest))]))

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol) (type : T) (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol) (var1-type : T)
         (var2-name : symbol) (var2-type : T)
         (rest : TypeEnv)])

(define (get-type name env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable")]
    [aBind (bound-name t rest) (if (symbol=? name bound-name)
                                   t
                                   (get-type name rest))]
    [tBind (n v1n v1t v2n v2t r) (get-type name r)]))

(define (find-type-id tyid env)
  (type-case TypeEnv env
    [mtEnv () (error 'find-type-id "no type")]
    [aBind (bound-name t rest) (find-type-id tyid rest)]
    [tBind (type-name v1n v1t v2n v2t rest) (if (symbol=? tyid type-name)
                                                env
                                                (find-type-id tyid rest))]))

(define (validtype type env)
  (type-case T type
    [numT () (mtEnv)]
;    [boolT () (mtEnv)]
    [arrowT (a r) (begin (validtype a env)
                         (validtype r env))]
;    [crossT (f s) (begin (validtype f env)
;                         (validtype s env))]
    [idT (name) (find-type-id name env)]
    [varT (is) (mtEnv)]))


(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))


(define (unify! t1 t2 expr)
  (type-case T t1
    [varT (is1) (type-case (Option T) (unbox is1)
                  [none () (local [(define t3 (resolve t2))]
                             (if (eq? t1 t3)
                                 (values)
                                 (if (occur? t1 t3)
                                     (error 'unify "occur")
                                     (begin (set-box! is1 (some t3))
                                            (values)))))]
                  [some (t3) (unify! t3 t2 expr)])]
    
    [else (type-case T t2
            [varT (is2) (unify! t2 t1 expr)]
            [arrowT (arg res) (type-case T t1
                                [arrowT (arg2 res2) (begin (unify! arg arg2 expr)
                                                           (unify! res res2 expr))]
                                [else (error 'typeunity "t1 not arrowT")])]
            [else (if (equal? t1 t2)
                      (values)
                      (error 'typecheck "not equal"))])]))

(define (resolve t)
  (type-case T t
    [varT (is) (type-case (Option T) (unbox is)
                 [none () t]
                 [some (t2) (resolve t2)])]
    [else t]))

; t1 is usually a varT (none)
(define (occur? t1 t2)
  (type-case T t2
    [arrowT (arg res) (or (occur? t1 arg) (occur? t1 res))]
    [varT (is) (type-case (Option T) (unbox is)
                 [none () (eq? t1 t2)]
                 [some (t3) (occur? t1 t3)])]
    [else false]))

(define (occur-id? t1 t2)
  (type-case T t2
    [arrowT (arg res) (or (occur-id? t1 arg) (occur-id? t1 res))]
    [varT (is) (type-case (Option T) (unbox is)
                 [none () false]
                 [some (t3) (occur? t1 t3)])]
    [idT (tyid) (equal? t1 t2)]
    [else false]))
   



(define typecheck : (TIFAE TypeEnv -> T)
  (lambda (tifae env)
    (type-case TIFAE tifae
      [num (n) (numT)]
      [add (l r) (begin
                   (unify! (typecheck l env) (numT) l)
                   (unify! (typecheck r env) (numT) r)
                   (numT))]
      [sub (l r) (begin
                   (unify! (typecheck l env) (numT) l)
                   (unify! (typecheck r env) (numT) r)
                   (numT))]
      [id (x) (get-type x env)]
      [fun (param paramte body) (local [(define paramT (parse-te paramte))]
                                  (arrowT paramT (typecheck body (aBind param paramT env))))]
      [app (f a) (local [(define result-type (varT (box (none))))]
                   (begin
                     (unify! (arrowT (typecheck a env) result-type)
                             (typecheck f env)
                             f)
                     result-type))]
      [withtype (tyid var1-name var1-te var2-name var2-te body)
                (local [(define v1t (parse-te var1-te))
                        (define v2t (parse-te var2-te))
                        (define new-env (tBind tyid var1-name v1t var2-name v2t env))]
                  (begin (validtype v1t new-env)
                         (validtype v2t new-env)
                         (local [(define t-final (typecheck body (aBind var1-name (arrowT v1t (idT tyid))
                                                                        (aBind var2-name (arrowT v2t (idT tyid)) new-env))))]
                           (if (occur-id? (idT tyid) t-final)
                               (error 'typecheck "occur")
                               t-final))))]
      [cases (tyid dispatch-expr var1-name bind1-name var1-body var2-name bind2-name var2-body)
        (local [(define bind (find-type-id tyid env))]
          (if (and (equal? (tBind-var1-name bind) var1-name)
                   (equal? (tBind-var2-name bind) var2-name))
              (begin
                (unify! (typecheck dispatch-expr env) (idT tyid) dispatch-expr)
                (unify! (typecheck var1-body (aBind bind1-name (tBind-var1-type bind) env))
                        (typecheck var2-body (aBind bind2-name (tBind-var2-type bind) env))
                        var2-body)
                (typecheck var2-body (aBind bind2-name (tBind-var2-type bind) env)))
              (error 'typecheck "defined var names and used var names are different")))])))
      
      
(define some-env (aBind 'x (varT (box (none))) (mtEnv)))
(define a1 (get-type 'x some-env))
(define a2 (get-type 'x some-env))
(define a3 (varT (box (some a1))))




(test/exn (typecheck (app (withtype 'foo 'a (numTE) 'b (numTE)
                          (fun 'x (idTE 'foo) 
                               (cases 'foo (id 'x)
                                 'a 'n (add (id 'n) (num 3))
                                 'b 'n (add (id 'n) (num 4)))))
                (withtype 'foo 'c (arrowTE (numTE) (numTE)) 'd (numTE) (app (id 'c) (fun 'y (numTE) (id 'y))))) (mtEnv))
          "occur")
(typecheck (withtype 'foo 'c (arrowTE (numTE) (numTE)) 'd (numTE) (app (id 'c) (fun 'y (numTE) (id 'y)))) (mtEnv))

(typecheck (fun 'x (guessTE) (add (id 'x) (num 1))) (mtEnv))
(typecheck (fun 'y (guessTE) (id 'y)) (mtEnv))
(typecheck (app (fun 'y (guessTE) (id 'y)) (fun 'x (guessTE) (add (id 'x) (num 1)))) (mtEnv))
(typecheck (fun 'y (guessTE) (app (id 'y) (num 7))) (mtEnv))
(typecheck (fun 'x (guessTE) (app (id 'x) (id 'x))) (mtEnv))