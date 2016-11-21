#lang plai
; defining type WAE
(define-type WAE
  [num  (n number?)]
  [add  (lhs WAE?) (rhs WAE?)]
  [sub  (lhs WAE?) (rhs WAE?)]
  [with (name symbol?) (named-expr WAE?) (body WAE?)]
  [id   (name symbol?)])

; alph-sort : list of symbols -> list of symbols
; to sort a list into alphabetical order.
(define (symbol<? a b) (string<? (symbol->string a) (symbol->string b)))
(define (alph-sort l) (sort l symbol<?))


; Prob 1.
; free-ids : WAE -> list of symbols
; to find free identifiers from a given WAE, we should find "id x" identity that is not bounded by "with x" command.
(define (free-ids wae)
  (if (WAE? wae)
      (alph-sort
       (remove-duplicates
        (type-case WAE wae
          [num (n) empty]
          [add (l r) (append (free-ids l) (free-ids r))]
          [sub (l r) (append (free-ids l) (free-ids r))]
          [with (x i b) (append (free-ids i) 
                                (if (eq? (member x (free-ids b)) #f) (free-ids b) (remove x (free-ids b))))]
          [id (s) (list s)])))
      (error "ERROR : NOT WAE")))

(test/exn (free-ids 7) "ERROR : NOT WAE")
(test (free-ids (with 'x (num 5) (add (id 'x) (id 'y)))) '(y))
(test (free-ids (sub (sub (id 'x) (id 'a)) (id 't))) '(a t x))
(test (free-ids (with 'a (num 5) (id 'b))) '(b))


; Prob 2.
; binding-ids : WAE -> list of symbols
; to find binding identifiers from a given WAE, we should look for "with x" command.
(define (binding-ids wae)
  (if (WAE? wae)
      (alph-sort
       (remove-duplicates
        (type-case WAE wae
          [num (n) empty]
          [add (l r) (append (binding-ids l) (binding-ids r))]
          [sub (l r) (append (binding-ids l) (binding-ids r))]
          [with (x i b) (append (list x) (binding-ids i) (binding-ids b))]
          [id (s) empty])))
      (error "ERROR : NOT WAE")))

(test/exn (binding-ids 17) "ERROR : NOT WAE")
(test (binding-ids (num 16)) empty)
(test (binding-ids (with 'x (add (id 'x) (id 'a)) (sub (id 'x) (num 7)))) '(x))


; Prob 3.
; bound-ids : WAE -> list of symbols
; to find bound identifiers from a given WAE, we should look for "id x" keyword that is bounded by "with x" command.
(define (bound-ids wae)
  (if (WAE? wae)
      (alph-sort
       (remove-duplicates
        (type-case WAE wae
          [num (n) empty]
          [add (l r) (append (bound-ids l) (bound-ids r))]
          [sub (l r) (append (bound-ids l) (bound-ids r))]
          [with (x i b) (append (bound-ids i)
                                (if (eq? (member x (free-ids b)) #f) empty (list x))
                                (bound-ids b))]
          [id (s) empty])))
      (error "ERROR : NOT WAE")))

(test/exn (bound-ids 3) "ERROR : NOT WAE")
(test (bound-ids (with 'x (num 7) (add (id 'x) (with 'y (num 6) (id 'y))))) '(x y))
(test (bound-ids (add (id 'x) (sub (num 8) (with 'z (num 8) (id 'z))))) '(z))
(test (bound-ids (with 'b (id 'a) (add (num 2) (with 'a (num 8) (add (id 'b) (id 'c)))))) '(b))