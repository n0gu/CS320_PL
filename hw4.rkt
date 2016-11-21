#lang plai

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

;; PWAE abstract syntax trees
(define-type PWAE
  [num  (num (listof number?))]
  [pooh (nums list?) (op symbol?)]
  [add  (left PWAE?) (right PWAE?)]
  [sub  (left PWAE?) (right PWAE?)]
  [with (name symbol?) (init PWAE?) (body PWAE?)]
  [id   (name symbol?)])

; parse-sexpr : sexpr -> PWAE
;; to convert s-expressions into PWAEs
;; parse-nums : listof sexpr -> listof PWAE, a local function defined to parse pooh arguments.
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num (list sexp))]
    [(? (non-empty-listof number?)) (num sexp)]
    [(list 'pooh nums ..2 op)
     (local [(define (parse-nums l)
       (if (empty? l) empty (append (list (parse-sexpr (first l))) (parse-nums (rest l)))))]
       (pooh (parse-nums nums) op))]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?) (id sexp)]
    [else (error 'parse "bad syntax: ~a" sexp)]))

;; parses a string containing a PWAE expression to a PWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
;; subst-nums : listof PWAE -> listof PWAE, a local function defined to substitute pooh arguments.
(define (subst expr from to)
  (type-case PWAE expr
    [num (n)   expr]
    [pooh (nums op)
          (local [(define (subst-nums l)
                    (cond
                      [(= (length l) 1) (list (subst (first l) from to))]
                      [else (append (subst-nums (drop-right l 1)) (list (subst (last l) from to)))]))]
            (pooh (subst-nums nums) op))]                   
    [add (l r) (add (subst l from to) (subst r from to))]
    [sub (l r) (sub (subst l from to) (subst r from to))]
    [id (name) (if (symbol=? name from) (num to) expr)]
    [with (bound-id named-expr bound-body)
          (with bound-id
                (subst named-expr from to)
                (if (symbol=? bound-id from)
                    bound-body
                    (subst bound-body from to)))]))

;; evaluates WAE expressions by reducing them to numbers
;; eval-helper : symbol PWAE PWAE -> PWAE, a local function defined to evaluate pooh arguments.
;; with this eval-helper, recursively evaluate pooh arguments.
(define (eval expr)
  (type-case PWAE expr
    [num (n) n]
    [pooh (nums op)
          (local [(define (eval-helper op lp rp)
                    (cond
                      [(symbol=? op '+) (bin-op + (eval lp) (eval rp))]
                      [(symbol=? op '-) (bin-op - (eval lp) (eval rp))]))]
          (cond
            [(> (length nums) 2) (eval-helper op (pooh (drop-right nums 1) op) (last nums))]
            [(= (length nums) 2) (eval-helper op (first nums) (last nums))]))]                         
    [add (l r) (bin-op + (eval l) (eval r))]
    [sub (l r) (bin-op - (eval l) (eval r))]
    [with (bound-id named-expr bound-body)
          (eval (subst bound-body
                       bound-id
                       (eval named-expr)))]
    [id (name) (error 'eval "free identifier: ~s" name)]))

; run : string -> listof number
;; evaluate a WAE program contained in a string
(define (run str)
  (eval (parse str)))

; bin-op : op (listof PWAE) (listof PWAE) -> PWAE
;; defined to calculate listed PWAE numbers.
(define (bin-op op ls rs)
  (define (helper l rs)
    ;; f : number -> number
    (define f (lambda (rs) (op l rs)))
    (map f rs))
  (if (null? ls)
    null
    (append (helper (first ls) rs) (bin-op op (rest ls) rs))))



;; test area
(test (run "{+ {2 1} {3 4}}") '(5 6 4 5))
(test (run "{+ {- {+ 1 3} 2} {10 -10}}") '(12 -8))
(test (run "{+ 3 7}") '(10))
(test (run "{- 10 {3 5}}") '(7 5))
(test (run "{with {x {+ 5 5}} {+ x x}}") '(20))

(test (run "{with {x 2} {- {+ x x} x}}") '(2))
(test/exn (run "{with x = 2 {+ x 3}}") "bad syntax")
(test/exn (run "{bleh}") "bad syntax")


(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh 1 2 -}") '(-1))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{with {x {with {x 20} {pooh 1 x +}}} {with {y 10} {pooh x y -}}}") '(11))
(test (run "{with {x {pooh 1 2 3 4 5 +}} x}") '(15))
(test (run "{pooh {with {x {pooh {1 2} {3 4} 1 +}} x} 2 3 -}") '(0 1 1 2))
(test (run "{pooh 1 2 3 4 5 +}") '(15))
(test (run "{pooh {1 2 3} {4 5} -}") '(-3 -4 -2 -3 -1 -2))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh 1 2 3 4 +}") '(10))
(test (run "{pooh {3 4} {-4 0} 5 +}") '(4 8 5 9))
(test (run "{pooh 1 2 3 4 -}") '(-8))
(test (run "{pooh {4 1} 1 {5 6 7} -}") '(-2 -3 -4 -5 -6 -7))
(test (run "{+ {pooh 1 {4 9} -3 {2 0 1} +} {- {pooh {3 4} {2} -} 4}}") '(1 2 -1 0 0 1 6 7 4 5 5 6))
(test (run "{pooh 1 {pooh 1 2 -} 3 +}") '(3))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh {2 1} {3 4} +}") '(5 6 4 5))
(test (run "{with {x {1 2}} {pooh x {+ {1 2} 1} -}}") '(-1 -2 0 -1))
(test (run "{with {x {1 2}} {pooh x {pooh {1 2} 1 +} -}}") '(-1 -2 0 -1))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{with {x {with {y {1 -2}} {pooh 1 y 2 -}}} {+ x x}}") '(-4 -1 -1 2))
(test (run "{with {x {pooh 8 7 -}} {with {x 10} {+ x 3}}}") '(13))
(test/exn (run "{pooh x 7 +}") "free identifier: x")