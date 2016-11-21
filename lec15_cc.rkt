#lang plai

(define table empty)
(define (remember v)
  (local [(define n (length table))]
    (begin (set! table (append table (list v)))
           n)))
(define (lookup key)
  (list-ref table key))


; implementing web-read, implicit continuation version
(define (web-read prompt)
          (let/cc cont
            (local [(define key (remember cont))]
              (error 'web-read
                     "~a To continue, call resume with ~a and value"
                     prompt key))))
(define (resume key val)
  (local [(define cont (lookup key))]
    (cont val)))

(define (h)
  (+ (web-read "First")
     (web-read "Second")))




; call twice
(define (web-pause prompt)
  (let/cc cont
    (local [(define key (remember cont))]
      (error 'web-pause
             "~a; to continue, call p-resume with ~a"
             prompt key))))
(define (p-resume key)
  (local [(define cont (lookup key))]
    (cont)))

(define (i)
  (web-pause (h))
  (h))


; using map
(define (web-read-each prompts)
  (map web-read prompts))

(define (m)
  (apply format "my ~a saw a ~a rock"
         (web-read-each '("noun" "adjective"))))


; application
(define (plus)
  (apply + (web-read-each '("First" "Second"))))