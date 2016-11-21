#lang plai

; using local define version
(local [(define fac
          (lambda (n)
            (if (zero? n)
                1
                (* n (fac (- n 1))))))]
  (fac 5))


; let version
(let ([facX
       (lambda (facY n)
         (if (zero? n)
                1
                (* n (facY facY (- n 1)))))])
  (facX facX 5))


; let version with wrap, n reduction
(let ([fac
       (let ([facX
              (lambda (facX)
                (lambda (n)
                  (if (zero? n)
                      1
                      (* n ((facX facX) (- n 1))))))])
         (facX facX))])
  (fac 5))


; making a skeleton code for recursive functions.
(let ([fac
       (let ([facX
              (lambda (facX)
                (let ([final (lambda (n)
                               ((facX facX) n))])
                  (lambda (n)
                    (if (zero? n)
                        1
                        (* n (final (- n 1)))))))])
         (facX facX))])
  (fac 5))

; skeleton function for making recursive function
; body is the whole lambda function body of a recursive functin.
(define (mk-rec body)
  (let ([fx
         (lambda (fx)
           (let ([final (lambda (n)
                          ((fx fx) n))])
             (body final)))])
    (fx fx)))
                           

; example: fibonacci
(let ([fibo
       (mk-rec
        (lambda (fibo)
          (lambda (n)
            (cond
              [(= 1 n) 1]
              [(= 2 n) 1]
              [else (+ (fibo (- n 1)) (fibo (- n 2)))]))))])
  (fibo 9))