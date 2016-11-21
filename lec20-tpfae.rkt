#lang plai-typed

; Lecture 20 - type, pair fae

(define-type TPFAE
  [num (n : number)]
  [add (l : TPFAE) (r : TPFAE)]
  [sub (l : TPFAE) (r : TPFAE)]
  [id (x : symbol)]
  [fun (param : symbol)
       (paramty : TE)
       (body : TPFAE)]
  [app (fun-expr : TPFAE) (arg-expr : TPFAE)]
  [pair (fst-expr : TPFAE) (snd-expr : TPFAE)]
  [fst (pair-expr : TPFAE)]
  [snd (pair-expr : TPFAE)])

(define-type TPFAE-value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : symbol) (body : TPFAE) (ds : DefrdSub)]
  [pairV (left : TPFAE-value) (right : TPFAE-value)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (arg : TE) (result : TE)]
  [crossTE (f : TE) (s : TE)])

(define-type T
  [numT]
  [boolT]
  [arrowT (arg : T) (result : T)]
  [crossT (f : T) (s : T)])

(define (parse-te te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (arg result) (arrowT (parse-te arg) (parse-te result))]
    [crossTE (f s) (crossT (parse-te f) (parse-te s))]))
    
(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol) (value : TPFAE-value) (rest : DefrdSub)])

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest) (if (symbol=? name sub-name)
                                  val
                                  (lookup name rest))]))

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol) (type : T) (rest : TypeEnv)])

(define (get-type name env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable")]
    [aBind (bound-name t rest) (if (symbol=? name bound-name)
                                   t
                                   (get-type name rest))]))


(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))


(define (interp tpfae ds)
  (type-case TPFAE tpfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (x) (lookup x ds)]
    [fun (param paramte body) (closureV param body ds)]
    [app (f a) (local [(define f-val (interp f ds))
                       (define a-val (interp a ds))]
                 (interp (closureV-body f-val) (aSub (closureV-param f-val)
                                                     a-val
                                                     (closureV-ds f-val))))]
    [pair (f s) (pairV (interp f ds) (interp s ds))]
    [fst (p) (pairV-left (interp p ds))]
    [snd (p) (pairV-right (interp p ds))]))


(define typecheck : (TPFAE TypeEnv -> T)
  (lambda (tpfae env)
    (type-case TPFAE tpfae
      [num (n) (numT)]
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
      [fun (param paramte body) (local [(define paramT (parse-te paramte))]
                                  (arrowT paramT (typecheck body (aBind param paramT env))))]
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
                 [crossT (f s) f]
                 [else (error 'typecheck "snd : p not pair")])])))


(define eval : (TPFAE -> TPFAE-value)
  (lambda (tpfae)
    (begin
      (try (typecheck tpfae (mtEnv))
           (lambda () (error 'eval "typecheck fail")))
      (interp tpfae (mtSub)))))

(test (interp (num 10)
              (mtSub))
      (numV 10))
(test (interp (add (num 10) (num 17))
              (mtSub))
      (numV 27))
(test (interp (sub (num 10) (num 7))
              (mtSub))
      (numV 3))
(test (interp (app (fun 'x (numTE) (add (id 'x) (num 12)))
                   (add (num 1) (num 17)))
              (mtSub))
      (numV 30))
(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))

(test (interp (app (fun 'x (numTE)
                        (app (fun 'f (arrowTE (numTE) (numTE))
                                  (add (app (id 'f) (num 1))
                                       (app (fun 'x (numTE)
                                                 (app (id 'f)
                                                      (num 2)))
                                            (num 3))))
                             (fun 'y (numTE)
                                  (add (id 'x) (id 'y)))))
                   (num 0))
              (mtSub))
      (numV 3))

(test/exn (interp (id 'x) (mtSub))
          "free variable")

(test (typecheck (num 10) (mtEnv))
      (numT))

(test (typecheck (add (num 10) (num 17)) (mtEnv))
      (numT))
(test (typecheck (sub (num 10) (num 7)) (mtEnv))
      (numT))

(test (typecheck (fun 'x (numTE) (add (id 'x) (num 12))) (mtEnv))
      (arrowT (numT) (numT)))

(test (typecheck (fun 'x (numTE) (fun 'y (boolTE) (id 'x))) (mtEnv))
      (arrowT (numT) (arrowT (boolT)  (numT))))

(test (typecheck (app (fun 'x (numTE) (add (id 'x) (num 12)))
                      (add (num 1) (num 17)))
                 (mtEnv))
      (numT))

(test (typecheck (app (fun 'x (numTE)
                           (app (fun 'f (arrowTE (numTE) (numTE))
                                     (add (app (id 'f) (num 1))
                                          (app (fun 'x (numTE) (app (id 'f) (num 2)))
                                               (num 3))))
                                (fun 'y (numTE)
                                     (add (id 'x)
                                          (id' y)))))
                      (num 0))
                 (mtEnv))
      (numT))


(test (interp (fst (pair (num 10) (num 8))) (mtSub)) (numV 10))
(test (interp (snd (pair (num 10) (num 8))) (mtSub)) (numV 8))
(test (typecheck (pair (num 10) (num 8)) (mtEnv)) (crossT (numT) (numT)))
(test (typecheck (add (num 1) (snd (pair (num 10) (num 8)))) (mtEnv)) (numT))
(test/exn (typecheck (fst (num 10)) (mtEnv)) "not")

(test/exn (typecheck (app (num 1) (num 2)) (mtEnv))
          "not")

(test/exn (typecheck (add (fun 'x (numTE) (num 12))
                          (num 2))
                     (mtEnv))
          "not")
  