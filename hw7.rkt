#lang plai

; Programming Language hw 7

;; string parser
(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
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
;;-------------------------------------

(define-type KCFAE
  [num (n number?)]
  [add (l KCFAE?) (r KCFAE?)]
  [sub (l KCFAE?) (r KCFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body KCFAE?)]
  [app (f KCFAE?) (a KCFAE?)])

(define-type CKCFAE
  [cnum (n number?)]
  [cadd (l CKCFAE?) (r CKCFAE?)]
  [csub (l CKCFAE?) (r CKCFAE?)]
  [cid (pos number?)]
  [cfun (body CKCFAE?)]
  [capp (f CKCFAE?) (a CKCFAE?)])

(define-type CKCFAE-Value
  [numV (n number?)]
  [closureV (body CKCFAE?) (ds list?)])

(define-type CDefrdSub
  [mtCSub]
  [aCSub (name symbol?) (rest CDefrdSub?)])

(define-type CKCFAE-Cont
  [mtK]
  [addSecondK (r CKCFAE?) (ds list?) (k CKCFAE-Cont?)]
  [doAddK     (v CKCFAE-Value?) (k CKCFAE-Cont?)]
  [subSecondK (r CKCFAE?) (ds list?) (k CKCFAE-Cont?)]
  [doSubK     (v CKCFAE-Value?) (k CKCFAE-Cont?)]
  [appArgK    (a CKCFAE?) (ds list?) (k CKCFAE-Cont?)]
  [doAppK     (v CKCFAE-Value?) (k CKCFAE-Cont?)])

(define (DefrdSub? x) true)



;; parse-sexpr : S-expr -> KCFAE
(define (parse-sexpr sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse-sexpr (second sexp))
                 (parse-sexpr (third sexp)))]
       [(-) (sub (parse-sexpr (second sexp))
                 (parse-sexpr (third sexp)))]
       [(fun) (fun (first (second sexp))
                   (parse-sexpr (third sexp)))]
       [else (app (parse-sexpr (first sexp))
                  (parse-sexpr (second sexp)))])]))

;; parse: string -> KCFAE
;; parses a string containing a KCFAE expression to a KCFAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; compile : KCFAE CDefrdSub -> CKCFAE
(define (compile kcfae ds)
  (type-case KCFAE kcfae
    [num (n) (cnum n)]
    [add (l r) (cadd (compile l ds) (compile r ds))]
    [sub (l r) (csub (compile l ds) (compile r ds))]
    [id (name) (cid (locate name ds))]
    [fun (param body) (cfun (compile body (aCSub param ds)))]
    [app (f a) (capp (compile f ds) (compile a ds))]))

;; locate : symbol CDefrdSub -> number
(define (locate name ds)
  (type-case CDefrdSub ds
    [mtCSub () (error 'locate "free variable")]
    [aCSub (sub-name rest-ds)
           (if (symbol=? sub-name name)
               0
               (+ 1 (locate name rest-ds)))]))

(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))

(define ckcfae-reg (cnum 0))
(define k-reg (mtK))
(define v-reg (numV 0))
(define ds-reg empty)

;; interp : -> CKCFAE-Value
(define (interp)
  (type-case CKCFAE ckcfae-reg
    [cnum (n) (begin
                (set! v-reg (numV n))
                (continue))]
    [cadd (l r) (begin
                  (set! ckcfae-reg l)
                  (set! k-reg (addSecondK r ds-reg k-reg))
                  (interp))]
    [csub (l r) (begin
                  (set! ckcfae-reg l)
                  (set! k-reg (subSecondK r ds-reg k-reg))
                  (interp))]
    [cid (pos) (begin
                 (set! v-reg (list-ref ds-reg pos))
                 (continue))]
    [cfun (b) (begin
                (set! v-reg (closureV b ds-reg))
                (continue))]
    [capp (f a) (begin
                  (set! ckcfae-reg f)
                  (set! k-reg (appArgK a ds-reg k-reg))
                  (interp))]))

;; continue : -> CKCFAE-Value
(define (continue)
  (type-case CKCFAE-Cont k-reg
    [mtK () v-reg]
    [addSecondK (r ds k) (begin
                           (set! ckcfae-reg r)
                           (set! ds-reg ds)
                           (set! k-reg (doAddK v-reg k))
                           (interp))]
    [doAddK (first-v k) (begin
                          (set! v-reg (num+ first-v v-reg))
                          (set! k-reg k)
                          (continue))]
    [subSecondK (r ds k) (begin
                           (set! ckcfae-reg r)
                           (set! ds-reg ds)
                           (set! k-reg (doSubK v-reg k))
                           (interp))]
    [doSubK (first-v k) (begin
                          (set! v-reg (num- first-v v-reg))
                          (set! k-reg k)
                          (continue))]
    [appArgK (a ds k) (begin
                        (set! ckcfae-reg a)
                        (set! ds-reg ds)
                        (set! k-reg (doAppK v-reg k))
                        (interp))]
    [doAppK (fun-v k) (begin
                        (set! ckcfae-reg (closureV-body fun-v))
                        (set! ds-reg (cons v-reg (closureV-ds fun-v)))
                        (set! k-reg k)
                        (interp))]))

;; init : void -> void
(define (init)
  (set! k-reg (mtK))
  (set! v-reg (numV 0))
  (set! ds-reg empty))

;; run : string -> CKCFAE-Value
;; evaluate a KCFAE program contained in a string
(define (run str)
  (begin
    (set! ckcfae-reg (compile (parse str) (mtCSub)))
    (init)
    (interp)))


(test (run "{- 20 {{fun {x} {+ x x}} 17}}") (numV -14))
(test (run "{fun {x} {+ 1 x}}") (closureV (cadd (cnum 1) (cid 0)) empty))
(test (run "{{fun {y} {{fun {x} {+ y x}} 8}} 2}") (numV 10))
(test (run "{{{fun {y} {fun {x} {+ y x}}} 2} 8}") (numV 10))
(test (run "10") (numV 10))
(test (run "{+ 10 7}") (numV 17))
(test (run "{- 10 7}") (numV 3))
(test (run "{{fun {x} {+ x 12}} {+ 1 17}}") (numV 30))
(test (run "{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}}
                       {fun {y} {+ x y}}}} 0}") (numV 3))
