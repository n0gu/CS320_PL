#lang plai-typed

; Lecture 21, 22 - TV, RC fae

(define-type TVRCFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TVRCFAE) (r : TVRCFAE)]
  [sub (l : TVRCFAE) (r : TVRCFAE)]
  [id (x : symbol)]
  [fun (param : symbol)
       (paramty : TE)
       (body : TVRCFAE)]
  [app (fun-expr : TVRCFAE) (arg-expr : TVRCFAE)]
  [pair (fst-expr : TVRCFAE) (snd-expr : TVRCFAE)]
  [fst (pair-expr : TVRCFAE)]
  [snd (pair-expr : TVRCFAE)]
  [if0 (test-expr : TVRCFAE) (then-expr : TVRCFAE) (else-expr : TVRCFAE)]
  [rec (id : symbol) (idte : TE) (rec-body : TVRCFAE) (body : TVRCFAE)]
  [withtype (tyid : symbol)
            (var1-name : symbol) (var1-ty : TE)
            (var2-name : symbol) (var2-ty : TE)
            (body-expr : TVRCFAE)]
  [cases (name : symbol) (dispatch-expr : TVRCFAE)
    (var1-name : symbol) (bind1-name : symbol) (var1-body : TVRCFAE)
    (var2-name : symbol) (bind2-name : symbol) (var2-body : TVRCFAE)])
            

(define-type TVRCFAE-value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : symbol) (body : TVRCFAE) (ds : DefrdSub)]
  [pairV (left : TVRCFAE-value) (right : TVRCFAE-value)]
  [variantV (right? : boolean) (value : TVRCFAE-value)]
  [constructV (right? : boolean)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (arg : TE) (result : TE)]
  [crossTE (f : TE) (s : TE)]
  [idTE (name : symbol)])

(define-type T
  [numT]
  [boolT]
  [arrowT (arg : T) (result : T)]
  [crossT (f : T) (s : T)]
  [idT (name : symbol)])

(define (parse-te te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (arg result) (arrowT (parse-te arg) (parse-te result))]
    [crossTE (f s) (crossT (parse-te f) (parse-te s))]
    [idTE (name) (idT name)]))
    
(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol) (value : TVRCFAE-value) (rest : DefrdSub)]
  [aRecSub (name : symbol) (value-holder : (boxof TVRCFAE-value)) (rest : DefrdSub)])

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest) (if (symbol=? name sub-name)
                                  val
                                  (lookup name rest))]
    [aRecSub (sub-name val-box rest) (if (symbol=? name sub-name)
                                         (unbox val-box)
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
    [mtEnv () (error name "free variable")]
    [aBind (bound-name t rest) (if (symbol=? name bound-name)
                                   t
                                   (get-type name rest))]
    [tBind (tyid v1n v1t v2n v2t rest) (get-type name rest)]))

(define (validtype type env)
  (type-case T type
    [numT () (mtEnv)]
    [boolT () (mtEnv)]
    [arrowT (a r) (begin (validtype a env)
                         (validtype r env))]
    [crossT (f s) (begin (validtype f env)
                         (validtype s env))]
    [idT (name) (find-type-id name env)]))

(define (find-type-id name env)
  (type-case TypeEnv env
    [mtEnv () (error 'find-type-id "no type")]
    [aBind (bound-name t rest) (find-type-id name rest)]
    [tBind (type-name v1n v1t v2n v2t rest) (if (symbol=? name type-name)
                                                env
                                                (find-type-id name rest))]))


(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))


(define (interp tvrcfae ds)
  (type-case TVRCFAE tvrcfae
    [num (n) (numV n)]
    [bool (b) (boolV b)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (x) (lookup x ds)]
    [fun (param paramte body) (closureV param body ds)]
    [app (f a) (local [(define f-val (interp f ds))
                       (define a-val (interp a ds))]
                 (type-case TVRCFAE-value f-val
                   [closureV (param body ds) (interp body (aSub param a-val ds))]
                   [constructV (right?) (variantV right? a-val)]
                   [else (error 'interp "no func")]))]
    [pair (f s) (pairV (interp f ds) (interp s ds))]
    [fst (p) (pairV-left (interp p ds))]
    [snd (p) (pairV-right (interp p ds))]
    [if0 (test then-e else-e) (if (equal? (numV 0) (interp test ds))
                                  (interp then-e ds)
                                  (interp else-e ds))]
    [rec (id idte rec-body body) (local [(define value-holder (box (numV 0)))
                                         (define new-ds (aRecSub id value-holder ds))]
                                   (begin
                                     (set-box! value-holder (interp rec-body new-ds))
                                     (interp body new-ds)))]
    [withtype (tyid var1-name var1-te var2-name var2-te body)
              (interp body (aSub var1-name (constructV false)
                                 (aSub var2-name (constructV true) ds)))]
    [cases (tyid dispatch-expr var1-name bind1-name var1-body var2-name bind2-name var2-body)
      (type-case TVRCFAE-value (interp dispatch-expr ds)
        [variantV (right? val) (if right?
                                   (interp var2-body (aSub bind2-name val ds))
                                   (interp var1-body (aSub bind1-name val ds)))]
        [else (error 'interp "cases not found")])]))


(define typecheck : (TVRCFAE TypeEnv -> T)
  (lambda (tvrcfae env)
    (type-case TVRCFAE tvrcfae
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r) (type-case T (typecheck l env)
                   [numT () (type-case T (typecheck r env)
                              [numT () (numT)]
                              [else (error 'typecheck "add : r not num")])]
                   [else (error 'typecheck "add : l not num")])]
      [sub (l r) (type-case T (typecheck l env)
                   [numT () (type-case T (typecheck r env)
                              [numT () (numT)]
                              [else (error 'typecheck "sub : r not num")])]
                   [else (error 'typecheck "sub : l not num")])]
      [id (x) (get-type x env)]
      [fun (param paramte body) (local [(define paramT (parse-te paramte))] ;! for TV system, validtype is added
                                  (begin (validtype paramT env)
                                         (arrowT paramT (typecheck body (aBind param paramT env)))))]
      [app (f a) (type-case T (typecheck f env)
                   [arrowT (arg result) (if (equal? arg (typecheck a env))
                                            result
                                            (error 'typecheck "app : arg doesn't match"))]
                   [else (error 'typecheck "app : f not function")])]
      [pair (f s) (crossT (typecheck f env) (typecheck s env))]
      [fst (p) (type-case T (typecheck p env)
                 [crossT (f s) f]
                 [else (error 'typecheck "fst : p not pair")])]
      [snd (p) (type-case T (typecheck p env)
                 [crossT (f s) s]
                 [else (error 'typecheck "snd : p not pair")])]
      [if0 (test then-e else-e) (type-case T (typecheck test env)
                                  [numT () (if (equal? (typecheck then-e env) (typecheck else-e env))
                                               (typecheck then-e env)
                                               (error 'typecheck "then and else not same"))]
                                  [else (error 'typecheck "test not num")])]
      [rec (id idte rec-body body) (local [(define rec-type (parse-te idte))
                                           (define new-env (aBind id rec-type env))]
                                     (if (equal? rec-type (typecheck rec-body new-env))
                                         (typecheck body new-env)
                                         (error 'typecheck "rec function not match")))]
      [withtype (tyid var1-name var1-te var2-name var2-te body)
                (local [(define v1t (parse-te var1-te))
                        (define v2t (parse-te var2-te))
                        (define new-env (tBind tyid var1-name v1t var2-name v2t env))]
                  (begin (validtype v1t new-env)
                         (validtype v2t new-env)
                         (local [(define t-final (typecheck body (aBind var1-name (arrowT v1t (idT tyid))
                                                                        (aBind var2-name (arrowT v2t (idT tyid)) new-env))))]
                           (if (occur? t-final (idT tyid))
                               (error 'typecheck "occur")
                               t-final))))]
      [cases (tyid dispatch-expr var1-name bind1-name var1-body var2-name bind2-name var2-body)
        (local [(define bind (find-type-id tyid env))]
          (if (and (equal? (tBind-var1-name bind) var1-name)
                   (equal? (tBind-var2-name bind) var2-name))
              (type-case T (typecheck dispatch-expr env)
                [idT (name) (if (symbol=? name tyid)
                                (if (equal? (typecheck var1-body (aBind bind1-name (tBind-var1-type bind) env))
                                            (typecheck var2-body (aBind bind2-name (tBind-var2-type bind) env)))
                                    (typecheck var1-body (aBind bind1-name (tBind-var1-type bind) env))
                                    (error 'typecheck "var1 body and var2 body are not the same"))
                                (error 'typecheck "dispatch-expr's type id is not tyid"))]
                [else (error 'typecheck "dispatch-expr is not idT")])
              (error 'typecheck "var1, var2 name not match")))])))
                     
; t2 usually idT. only called when t2 = idt..
(define (occur? t1 t2)
  (type-case T t1
    [arrowT (arg res) (or (occur? arg t2) (occur? res t2))]
    [crossT (f s) (or (occur? f t2) (occur? s t2))]
    [idT (name) (equal? t1 t2)]
    [else false]))

(define eval : (TVRCFAE -> TVRCFAE-value)
  (lambda (tpfae)
    (begin
      (try (typecheck tpfae (mtEnv))
           (lambda () (error 'eval "typecheck fail")))
      (interp tpfae (mtSub)))))

    

;buggy expr
(typecheck (rec 'f (arrowTE (numTE) (numTE)) (id 'f) (app (id 'f) (num 10))) (mtEnv))

;another buggy expr - fixed!
(test/exn (typecheck (app (withtype 'foo 'a (numTE) 'b (numTE)
                          (fun 'x (idTE 'foo) 
                               (cases 'foo (id 'x)
                                 'a 'n (add (id 'n) (num 3))
                                 'b 'n (add (id 'n) (num 4)))))
                (withtype 'foo 'c (arrowTE (numTE) (numTE)) 'd (numTE) (app (id 'c) (fun 'y (numTE) (id 'y))))) (mtEnv))

          "occur")


(typecheck (withtype 'numlist 'empty (numTE) 'cons (crossTE (numTE) (idTE 'numlist))
          (rec 'len (arrowTE (idTE 'numlist) (numTE))
            (fun 'l (idTE 'numlist) (cases 'numlist (id 'l)
                                      'empty 'n (num 0)
                                      'cons 'fxr (add (num 1) (app (id 'len) (snd (id 'fxr))))))
            (app (id 'len) (app (id 'cons) (pair (num 1) (app (id 'empty) (num 0)))))))
        (mtEnv)
        )



(typecheck (withtype 'fruit 'apple (numTE) 'banana (numTE)
                     (withtype 'color 'banana (numTE) 'apple (numTE)
                               (cases 'fruit (app (id 'apple) (num 10))
                                 'apple 'n (id 'n)
                                 'banana 'n (add (id 'n) (num 100)))))
           (mtEnv))



; makes error - good.
(typecheck
 (withtype 'fruit 'apple (numTE) 'banana (numTE) (app (withtype 'color 'apple (arrowTE (numTE) (numTE)) 'banana (boolTE)
                                                                (fun 'x (idTE 'fruit) (cases 'fruit (id 'x)
                                                                                        'apple 'n (add (id 'n) (num 3))
                                                                                        'banana 'n (add (id 'n) (num 4)))))
                                                      (app (id 'banana) (bool true))))
 (mtEnv))