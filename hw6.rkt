#lang plai

; Programming Language hw 6

;; defining KCFAE with multi-args, try & catch
(define-type KCFAE
  [num (n number?)]
  [add (lhs KCFAE?)
       (rhs KCFAE?)]
  [sub (lhs KCFAE?)
       (rhs KCFAE?)]
  [id (name symbol?)]
  [fun (params (listof symbol?))
       (body KCFAE?)]
  [app (fun-expr KCFAE?)
       (arg-exprs (listof KCFAE?))]
  [if0 (test KCFAE?)
       (then KCFAE?)
       (else KCFAE?)]
  [withcc (name symbol?)
          (body KCFAE?)]
  [try (try-expr KCFAE?)
       (catch-expr KCFAE?)]
  [throw] )

(define-type KCFAE-Value
  [numV (n number?)]
  [closureV (params (listof symbol?))
            (body KCFAE?)
            (sc DefrdSub?)]
  [contV (proc procedure?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value KCFAE-Value?)
        (rest DefrdSub?)])

;; ----------------------------------------



; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) ( -> catch) -> alpha
; k is continuation, a job to do next.
; catch is a job to do when throw occurs.
(define (interp a-fae ds k catch)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num+ v1 v2)))
                                 catch))
                       catch)]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num- v1 v2)))
                                 catch))
                       catch)]
    [id (name) (k (lookup name ds))]
    [fun (params body-expr)
         (k (closureV params body-expr ds))]
    [app (fun-expr arg-exprs)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (type-case KCFAE-Value fun-val
                     [closureV (params body closure-ds)
                               (if (eq? (length params) (length arg-exprs))
                                   (interp-seqn arg-exprs ds
                                                (lambda (arg-vals)
                                                  (interp body
                                                          (match-sub params arg-vals closure-ds) ;match-subs creates ds with matched params and argvals
                                                          k
                                                          catch))
                                                catch)
                                   (error 'interp "number of params and args are not equal"))]
                     [contV (k)
                            (interp (first arg-exprs) ds ;cont functions still have only one argument
                                    (lambda (arg-val)
                                      (k arg-val))
                                    catch)]
                     [else (error 'interp "not a function")]))
                 catch)]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (numzero? v)
                       (interp then-expr ds k catch)
                       (interp else-expr ds k catch)))
                 catch)]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id
                          (contV k)
                          ds)
                    k
                    catch)]
    [try (try-expr catch-expr)
         (interp try-expr ds
                 k
                 (lambda () ;make a new "catch" continuation
                   (interp catch-expr ds
                           k
                           catch)))]
    [throw () (catch)])) ;continue to "catch"

; interp-seqn : (listof KCFAE) ds (listof KCFAE-values -> alpha) procedure -> listof KCFAE-values
; interp sequence of values and put them together in a list(especially for "app" arguments), and then continue to k
(define (interp-seqn seqn ds k catch)
  (if (empty? seqn)
      (k empty)
      (interp (first seqn) ds 
              (lambda (first-val) 
                (interp-seqn (rest seqn) ds
                             (lambda (rest-vals)
                               (k (append (list first-val) rest-vals)))
                             catch))
              catch)))

; match-sub : (listof symbol) (listof KCFAE-Value) DefrdSub -> DefrdSub
; to constitute aSub for multi-argument (match each param with arg one by one)
(define (match-sub params args ds)
      (if (empty? params)
          ds
          (aSub (first params) (first args) (match-sub (rest params) (rest args) ds))))

;; ----------------------------------------


;; helper functions
;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable ~a" name)]
    [aSub (sub-name num rest-sc)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-sc))]))

(test/exn (lookup 'x (mtSub)) "free variable")
(test (lookup 'x (aSub 'x (numV 9) (mtSub))) (numV 9))
(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 9) (mtSub)))) (numV 9))

;; interp-expr : KCFAE -> (or/c number symbol)
(define (interp-expr a-fae)
  (local [(define int-val (interp a-fae (mtSub) 
                                  (lambda (x) x)
                                  (lambda () 'uncaughtException)))]
    (if (KCFAE-Value? int-val)
        (type-case KCFAE-Value int-val
          [numV (n) n]
          [closureV (param body ds) 'function]
          [contV (k) 'function])
        int-val)))

;; ----------------------------------------


;; string parsing functions

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

; test cases for handling string 
(test/exn (string->sexpr 1) "expects argument of type <string>")
(test/exn (string->sexpr ".") "syntax error (bad contents)")
(test/exn (string->sexpr "{} {}") "bad syntax (multiple expressions)")

;; parse-sexpr : S-expr -> KCFAE
(define (parse-sexpr sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse-sexpr (second sexp)) (parse-sexpr (third sexp)))]
       [(-) (sub (parse-sexpr (second sexp)) (parse-sexpr (third sexp)))]
       [(fun) (fun (second sexp) (parse-sexpr (third sexp)))] ; parameters are treated as list
       [(if0) (if0 (parse-sexpr (second sexp))
                   (parse-sexpr (third sexp))
                   (parse-sexpr (fourth sexp)))]
       [(withcc) (withcc (second sexp) (parse-sexpr (third sexp)))]
       [(try) (try (parse-sexpr (second sexp)) (parse-sexpr (last sexp)))]
       [(throw) (throw)]
       [else (app (parse-sexpr (first sexp)) (map (lambda (val)
                                              (parse-sexpr val))
                                            (rest sexp)))])]))

(define (parse str)
  (parse-sexpr (string->sexpr str)))

(test (parse "3") (num 3))
(test (parse "x") (id 'x))
(test (parse "{+ 1 2}") (add (num 1) (num 2)))
(test (parse "{- 1 2}") (sub (num 1) (num 2)))
(test (parse "{fun {x} x}") (fun '(x) (id 'x)))
(test (parse "{1 2}") (app (num 1) (list (num 2))))
(test (parse "{if0 0 1 2}") (if0 (num 0) (num 1) (num 2)))
(test (parse "{withcc x 2}") (withcc 'x (num 2)))



;; ----------------------------------------
(define (run string)
  (interp-expr (parse string)))

(test/exn (run "{{fun {x y} {+ x y}} 1 x}") "free variable x")
(test/exn (run "{{fun {a} {a 3}} 2}") "not a function")
(test/exn (run "{try {{fun {x y} {+ x y}} 2 {throw} 4} catch 3}") "number of params and args are not equal")
(test (run "{try {+ 1 {throw}} catch {throw}}") 'uncaughtException)
(test (run "{try {try {throw} catch 3} catch 123}") 3)
(test (run "{try {try {throw} catch {throw}} catch 123}") 123)

(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{- 0 {withcc k {+ {k 10} 17}}}") -10)
(test (run "{- 0 {withcc k {+ 1 {withcc c {k {+ {c 10} 17}}}}}}") -11)
(test (run "{+ 5 {withcc k {+ 1000 {k 5}}}}") 10)
(test (run "{- 0 {withcc k {+ 15 {k 3}}}}") -3)
(test (run "{withcc a {- 0 {withcc b {b 15}}}}") -15)
(test (run "{{{fun {x y} {fun {c} {+ {+ x y} c}}} 1 2} 3}") 6)
(test (run "{if0 {withcc esc {+ 3 {esc 1}}} 10 {- 0 10}}") -10)
(test (run "{if0 {withcc esc {+ 3 {esc 0}}} 10 {- 0 10}}") 10)
(test (run "{- 0 {withcc esc {{fun {f} {f 3}} esc}}}") -3)
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{+ 3 {withcc k {+ 5 {k 9}}}}") 12)
(test (run "{{withcc k {fun {x y} {+ x y}}} 4 5}") 9)
(test (run "{+ {withcc k {k 5}} 4}" ) 9)
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}") 55) ; recursive function
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}") 100) ; exit from recursive function using continuation
(test (run "{withcc k {- 0 {k 100}}}" ) 100)
(test (run "{withcc k {k {- 0 100}}}" ) -100)
(test (run "{withcc k {k {+ 100 11}}}" ) 111)
(test (run "{{fun {a b c} {- {+ {withcc k {+ {k 100} a}} b} c}} 100 200 300}" ) 0)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{{withcc esc {{fun {x y} {fun {z} {+ z y}}} 1 {withcc k {esc k}}}} 10}") 20)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {+ y {g g {- y 1}}}}} 10} catch 110}") 110) ; exit from recursive function using try-catch
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch y}}} 10}") 54) ; test for multiple recursive try-catch
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {done y}}}} 10}}") 2)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {throw}}}} 10} catch 20110464}") 20110464) ; recursive try-catch throwing (1)
(test (run "{try {{fun {x y z} {a b c}} 1 2 {throw}} catch 0}") 0)
(test (run "{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}") 8)
(test (run "{try {- 0 {withcc k {+ 3 {k {throw}}}}} catch 89}") 89)
(test (run "{try {+ 3 {withcc k {+ 1000 {k {throw}}}}} catch 11}") 11)
(test (run "{{fun {x y z} {try {+ 1 {+ x {throw}}} catch {+ y z}}} 1 2 3}") 5)
(test (run "{+ {try {- 10 {throw}} catch 3} 10}") 13)
(test (run "{try {if0 0 {throw} {+ 1 2}} catch {if0 10 1 {try {throw} catch 54}}}")   54)
(test (run "{try {withcc a {+ 1 {withcc b {throw}}}} catch 10}") 10)
(test (run "{try {- 0 {throw}} catch 5}") 5)
(test (run "{try {if0 {throw} 3 4} catch 5}") 5)
(test (run "{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}") -1)
(test (run "{try {try {throw} catch {throw}} catch 9}") 9)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}") 5)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}") 10)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}") 42)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}") 3)
(test (run "{withcc esc {try {+ {throw} {esc 3}} catch 4}}") 4)
(test (run "{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}") 15)
(test (run "{try {withcc x {+ {x 1} {throw}}} catch 0}") 1)
(test (run "{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}") 19)