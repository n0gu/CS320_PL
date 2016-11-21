#lang plai-typed

(define-type TMFAE
  [num (n : number)]
  [add (lhs : TMFAE)
       (rhs : TMFAE)]
  [sub (lhs : TMFAE)
       (rhs : TMFAE)]
  [id (name : symbol)]
  [fun (params : (listof symbol))
       (paramtys : (listof TE))
       (body : TMFAE)]
  [app (fun-expr : TMFAE)
       (arg-exprs : (listof TMFAE))]
  [with (names : (listof symbol))
        (nametys : (listof TE))
        (inits : (listof TMFAE))
        (body : TMFAE)]
  [try1 (try-expr : TMFAE)
        (catch-exprs : TMFAE)]
  [throw]
  [bool (b : boolean)]
  [and1 (lhs : TMFAE)
       (rhs : TMFAE)]
  [or1 (lhs : TMFAE)
      (rhs : TMFAE)]
  [not1 (bool-expr : TMFAE)]
  [eq (lhs : TMFAE)
      (rhs : TMFAE)]
  [ifthenelse (cond-expr : TMFAE)
              (then-expr : TMFAE)
              (else-expr : TMFAE)]
  [pair (first-expr : TMFAE)
        (second-expr : TMFAE)]
  [fst (pair-expr : TMFAE)]
  [snd (pair-expr : TMFAE)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (args : (listof TE))
           (result : TE)]
  [crossTE (first-type : TE)
           (second-type : TE)])

(define-type TMFAE-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [pairV (first-expr : TMFAE)
         (second-expr : TMFAE)]
  [closureV (params : (listof symbol))
            (body : TMFAE)
            (ds : DefrdSub)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : TMFAE-Value)
        (rest : DefrdSub)])

(define-type Type
  [anyT]
  [numT]
  [boolT]
  [arrowT (args : (listof Type))
          (result : Type)]
  [crossT (first-type : Type)
          (second-type : Type)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

;; ----------------------------------------

;; interp : TMFAE DefrdSub ( -> catch) -> TMFAE-Value
(define (interp tmfae ds catch)
  (type-case TMFAE tmfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds catch) (interp r ds catch))]
    [sub (l r) (num- (interp l ds catch) (interp r ds catch))]
    [id (name) (lookup name ds)]
    [fun (params param-te body-expr)
         (closureV params body-expr ds)]
    [app (fun-expr arg-exprs)
         (local [(define fun-val (interp fun-expr ds catch))
                 (define arg-vals (interp-seqn arg-exprs ds catch))]
           (interp (closureV-body fun-val)
                   (match-sub (closureV-params fun-val)
                              arg-vals
                              (closureV-ds fun-val))
                   catch))]
    [with (names nametys inits body)
          (interp body (match-sub names (interp-seqn inits ds catch) ds) catch)]
    [try1 (try-expr catch-expr) (interp try-expr ds (lambda ()
                                                      (interp catch-expr ds catch)))]
    [throw () (catch)]
    [bool (b) (boolV b)]
    [and1 (l r) (local [(define l-val (interp l ds catch))
                        (define r-val (interp r ds catch))]
                  (boolV (and (boolV-b l-val) (boolV-b r-val))))]
    [or1 (l r) (local [(define l-val (interp l ds catch))
                        (define r-val (interp r ds catch))]
                 (boolV (or (boolV-b l-val) (boolV-b r-val))))]
    [not1 (bool-expr) (boolV (not (boolV-b (interp bool-expr ds catch))))]
    [eq (l r) (local [(define l-val (interp l ds catch))
                        (define r-val (interp r ds catch))]
                (if (equal? l-val r-val)
                    (boolV true)
                    (boolV false)))]
    [ifthenelse (cond-expr then-expr else-expr) (local [(define c-val (interp cond-expr ds catch))]
                                                  (if (boolV-b c-val)
                                                      (interp then-expr ds catch)
                                                      (interp else-expr ds catch)))]
    [pair (f s) (pairV f s)]
    [fst (pair-expr) (interp (pairV-first-expr (interp pair-expr ds catch)) ds catch)]
    [snd (pair-expr) (interp (pairV-second-expr (interp pair-expr ds catch)) ds catch)]))

; interp-seqn : (listof TMFAE) ds ( -> catch) -> listof TMFAE-values
; interp sequence of tmfae and put them together in a list
(define (interp-seqn seqn ds catch)
  (if (empty? seqn)
      empty
      (cons (interp (first seqn) ds catch) (interp-seqn (rest seqn) ds catch))))

; match-sub : (listof symbol) (listof TMFAE-Value) DefrdSub -> DefrdSub
; to make aSub for multiple argument (match each param with arg one by one)
(define (match-sub params args ds)
  (if (empty? params)
      ds
      (aSub (first params) (first args) (match-sub (rest params) (rest args) ds))))


;; num-op : (number number -> number) -> (TFAE-Value TFAE-Value -> TFAE-Value)
(define (num-op op x y)
  (numV (op (numV-n x) (numV-n y))))

(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-ds)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-ds))]))

;; ----------------------------------------

(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]))

;; ----------------------------------------

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (a b) (arrowT (map parse-type a)
                           (parse-type b))]
    [crossTE (f s) (crossT (parse-type f)
                           (parse-type s))]))


                  
(define typecheck : (TMFAE TypeEnv -> Type)
  (lambda (tmfae env)
    (type-case TMFAE tmfae
      [num (n) (numT)]
      [add (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (numT)]
                           [else (error 'typecheck "no type")])]
                   [anyT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (numT)]
                           [else (error 'typecheck "no type")])]
                   [else (error 'typecheck "no type")])]
      [sub (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (numT)]
                           [else (error 'typecheck "no type")])]
                   [anyT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (numT)]
                           [else (error 'typecheck "no type")])]
                   [else (error 'typecheck "no type")])]
      [id (name) (get-type name env)]
      [fun (params tes body)
           (local [(define param-types (map parse-type tes))]
             (arrowT param-types
                     (typecheck body (match-env params param-types env))))]
      [app (fn args)
           (local [(define fn-type (typecheck fn env))
                   (define arg-types (typecheck-seqn args env))]
             (type-case Type fn-type
               [arrowT (param-types result-type)
                       (if (all-t-equal? param-types arg-types)
                           result-type
                           (error 'typecheck "no type"))]
               [anyT () (anyT)]
               [else (error 'typecheck "no type")]))]
      [with (names nametys inits body)
            (typecheck body (match-env names (map parse-type nametys) env))]
      [try1 (try-expr catch-expr)
            (local [(define t-type (typecheck try-expr env))
                    (define c-type (typecheck catch-expr env))]
              (check-and-merge-two-type t-type c-type))]
      [throw () (anyT)]
      [bool (b) (boolT)]
      [and1 (l r) (type-case Type (typecheck l env)
                    [boolT ()
                           (type-case Type (typecheck r env)
                             [boolT () (boolT)]
                             [anyT () (boolT)]
                             [else (error 'typecheck "no type")])]
                    [anyT ()
                          (type-case Type (typecheck r env)
                            [boolT () (boolT)]
                            [anyT () (boolT)]
                            [else (error 'typecheck "no type")])]
                    [else (error 'typecheck "no type")])]
      [or1 (l r) (type-case Type (typecheck l env)
                   [boolT ()
                          (type-case Type (typecheck r env)
                            [boolT () (boolT)]
                            [anyT () (boolT)]
                            [else (error 'typecheck "no type")])]
                   [anyT ()
                         (type-case Type (typecheck r env)
                           [boolT () (boolT)]
                           [anyT () (boolT)]
                           [else (error 'typecheck "no type")])]
                   [else (error 'typecheck "no type")])]
      [not1 (bool-expr) (type-case Type (typecheck bool-expr env)
                          [boolT () (boolT)]
                          [anyT () (boolT)]
                          [else (error 'typecheck "no type")])]
      [eq (l r) (type-case Type (typecheck l env)
                  [numT ()
                        (type-case Type (typecheck r env)
                          [numT () (boolT)]
                          [anyT () (boolT)]
                          [else (error 'typecheck "no type")])]
                  [anyT ()
                        (type-case Type (typecheck r env)
                          [numT () (boolT)]
                          [anyT () (boolT)]
                          [else (error 'typecheck "no type")])]
                  [else (error 'typecheck "no type")])]
      [ifthenelse (cond-expr then-expr else-expr)
                  (type-case Type (typecheck cond-expr env)
                    [boolT () (local [(define t1 (typecheck then-expr env))
                                      (define t2 (typecheck else-expr env))]
                                (check-and-merge-two-type t1 t2))]
                    [anyT () (local [(define t1 (typecheck then-expr env))
                                     (define t2 (typecheck else-expr env))]
                               (check-and-merge-two-type t1 t2))]
                    [else (error 'typecheck "no type")])]
      [pair (f s) (crossT (typecheck f env) (typecheck s env))]
      [fst (pair-expr) (type-case Type (typecheck pair-expr env)
                         [crossT (f s) f]
                         [anyT () (anyT)]
                         [else (error 'typecheck "no type")])]
      [snd (pair-expr) (type-case Type (typecheck pair-expr env)
                         [crossT (f s) s]
                         [anyT () (anyT)]
                         [else (error 'typecheck "no type")])])))

; t-equal? : Type Type -> boolean
; check if two types are equal (anyT could be anything)
(define (t-equal? t1 t2)
  (type-case Type t1
    [anyT () (type-case Type t2
               [else true])]
    [numT () (type-case Type t2
               [anyT () true]
               [numT () true]
               [else false])]
    [boolT () (type-case Type t2
                [anyT () true]
                [boolT () true]
                [else false])]
    [arrowT (args result) (type-case Type t2
                            [anyT () true]
                            [arrowT (args2 result2) (and (all-t-equal? args args2)
                                                             (t-equal? result result2))]
                            [else false])]
    [crossT (f s) (type-case Type t2
                    [anyT () true]
                    [crossT (f2 s2) (and (t-equal? f f2) (t-equal? s s2))]
                    [else false])]))

; all-t-equal? : (listof Type) (listof Type) -> boolean
; compare list of Type as above (used to compare arguments, etc)
(define (all-t-equal? list1 list2)
  (if (and (empty? list1) (empty? list2))
      true
      (if (t-equal? (first list1) (first list2))
          (all-t-equal? (rest list1) (rest list2))
          false)))

; check-and-merge-two-type : Type Type -> Type
; check if the two types are t-equal, and then merge them if one of them is anyT
(define (check-and-merge-two-type t1 t2)
  (if (t-equal? t1 t2)
      (type-case Type t1
        [anyT () t2]
        [arrowT (args result) (type-case Type t2
                                [anyT () t1]
                                [arrowT (args2 result2) (arrowT (map2 check-and-merge-two-type args args2)
                                                                (check-and-merge-two-type result result2))]
                                [else (error 'typecheck "should not get here")])]
        [crossT (f s) (type-case Type t2
                        [anyT () t1]
                        [crossT (f2 s2) (crossT (check-and-merge-two-type f f2)
                                                (check-and-merge-two-type s s2))]
                        [else (error 'typecheck "should not get here")])]
        [else t1])            
      (error 'typecheck "no type")))
                                
; typecheck-seqn : (listof TMFAE) TypeEnv -> (listof Type)
; typecheck sequence of TMFAE
(define (typecheck-seqn seqn env)
  (if (empty? seqn)
      empty
      (cons (typecheck (first seqn) env) (typecheck-seqn (rest seqn) env))))

; match-env : (listof symbol) (listof TMFAE-Value) TypeEnv -> TypeEnv
; to constitute aBind for multi-argument (match each param with arg one by one)
(define (match-env params pts env)
  (if (empty? params)
      env
      (aBind (first params) (first pts) (match-env (rest params) (rest pts) env))))
;; ----------------------------------------

(define run : (TMFAE -> TMFAE-Value)
  (lambda (tmfae)
    (interp tmfae (mtSub) (lambda () (error 'interp "unhandled")))))
(define eval : (TMFAE -> TMFAE-Value)
  (lambda (tmfae)
    (begin
      (try (typecheck tmfae (mtEnv))
           (lambda () (error 'type-error "typecheck")))
      (run tmfae))))



(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE))
                        (sub (id 'x) (id 'y))) (list (num 10) (num 20))))
      (numV -10))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                           (id 'y))
                      (list (num 10) (bool false)))
                 (mtEnv))
      (boolT))
(test/exn (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                               (id 'y))
                          (list (num 10) (num 10)))
                     (mtEnv))
          "no type")
(test (typecheck (throw) (mtEnv)) (anyT))
(test (typecheck (try1 (num 8) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 10)) (mtEnv)) (numT))
(test/exn (typecheck (try1 (num 8) (bool false)) (mtEnv)) "no type")
(test (typecheck (ifthenelse (throw) (num 1) (num 2)) (mtEnv)) (numT))
(test/exn (typecheck (app (throw) (list (ifthenelse (num 1) (num 2) (num 3)))) (mtEnv)) "no type")
(test/exn (typecheck (add (bool true) (throw)) (mtEnv)) "no type")
(test (typecheck (fst (throw)) (mtEnv)) (anyT))
(test (typecheck (ifthenelse (bool true) (pair (num 1) (throw)) (pair (throw) (bool false))) (mtEnv)) (crossT (numT) (boolT)))
(test (typecheck (add (throw) (throw)) (mtEnv)) (numT))
(test (typecheck (app (throw) (list (num 10) (num 10))) (mtEnv)) (anyT))
(test (typecheck (try1 (add (num 1) (throw)) (throw)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (num 2) (throw)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (throw) (num 2)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (throw) (throw)) (mtEnv)) (anyT))
(test (typecheck (pair (num 2) (bool false)) (mtEnv)) (crossT (numT) (boolT)))
(test (typecheck (pair (num 2) (throw)) (mtEnv)) (crossT (numT) (anyT)))
(test (typecheck (snd (throw)) (mtEnv)) (anyT))
(test (typecheck (snd (pair (num 2) (bool false))) (mtEnv)) (boolT))
(test (typecheck (fun empty empty (num 2)) (mtEnv)) (arrowT empty (numT)))
(test (typecheck (fun (list 'x) (list (numTE)) (throw)) (mtEnv)) (arrowT (list (numT)) (anyT)))
(test (typecheck (app (fun empty empty (num 2)) empty) (mtEnv)) (numT))
(test (typecheck (app (throw) (list (num 2) (bool false))) (mtEnv)) (anyT))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y))) (list (num 2) (num 3))) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (num 2)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (throw)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'x 'y 'z) (list (boolTE) (numTE) (numTE)) (list (bool false) (num 2) (num 3)) (ifthenelse (id 'x) (id 'y) (id 'z))) (mtEnv)) (numT))
(test (typecheck (with empty empty empty (num 2)) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (throw)) (num 2)) (mtEnv)) (numT))
(test (run (app (snd (ifthenelse (bool true) (pair (num 1) (fun (list 'x 'y 'z) (list (boolTE) (boolTE) (boolTE)) (ifthenelse (id 'x) (and1 (id 'y) (id 'z)) (not1 (id 'x)))))
                             (pair (num 1) (fun (list 'x 'y 'z) (list (boolTE) (boolTE) (boolTE)) (ifthenelse (id 'x) (or1 (id 'y) (id 'z)) (not1 (id 'x))))))) 
          (list (bool true) (bool false) (bool false)))) (boolV false))
(test/exn (run (app (snd (ifthenelse (bool true) (pair (num 1) (fun (list 'x 'y 'z) (list (boolTE) (boolTE) (boolTE)) (ifthenelse (id 'x) (and1 (id 'y) (id 'z)) (throw))))
                             (pair (num 1) (fun (list 'x 'y 'z) (list (boolTE) (boolTE) (boolTE)) (ifthenelse (id 'x) (or1 (id 'y) (id 'z)) (not1 (id 'x))))))) 
          (list (bool false) (bool false) (bool false)))) "interp: unhandled")
(test/exn (run (with (list 'x) (list (numTE)) (list (throw)) (num 2))) "interp: unhandled")
(test (typecheck (try1 (pair (num 1) (throw)) (pair (throw) (bool false))) (mtEnv)) (crossT (numT) (boolT)))