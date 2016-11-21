#lang plai
; Prob 1.
; COURSE : new type
; variant_ids are CS320, CS311, and CS330.
; CS320 has two attributes: quiz and homework, CS311 has one attribute: homework,
; and CS330 has two attributes: project and homework.
(define-type COURSE
  [CS320 (quiz integer?)
         (homework integer?)]
  [CS311 (homework integer?)]
  [CS330 (projoect integer?)
         (homework integer?)])

(define pl (CS320 6 10))
(define co (CS311 5))
(define os (CS330 4 6))

; Prob 2.
; have-homework : COURSE -> integer
; to see how many homeworks(programming assignments) the course has
(define (have-homework course)
  (type-case COURSE course
    [CS320 (q h) h]
    [CS311 (h) h]
    [CS330 (p h) h]))

(test (have-homework pl) 10)
(test (have-homework co) 5)
(test (have-homework os) 6)

; Prob 3.
; have-projects : COURSE -> boolean
; returns true only when given course is CS330 with more than or equal to two projects.
; otherwise, return false.
(define (have-projects course)
  (type-case COURSE course
    [CS320 (q h) #f]
    [CS311 (h) #f]
    [CS330 (p h) (>= p 2)]))

(test (have-projects pl) #f)
(test (have-projects co) #f)
(test (have-projects os) #t)

; Prob 4.
; name-pets : listof string -> listof string
; to change some input data (list of pets' species) into corresponding names.
; dog -> happy, cat -> smart, and pig -> pinky. otherwise, keep their species name.
(define (name-pets pets)
  (cond
    [(empty? pets) empty]
    [else (append (list(cond
                    [(symbol=? (first pets) 'dog) 'happy]
                    [(symbol=? (first pets) 'cat) 'smart]
                    [(symbol=? (first pets) 'pig) 'pinky]
                    [else (first pets)]))
                  (name-pets (rest pets)))]))

(test (name-pets '(dog cat pig tiger)) '(happy smart pinky tiger))

; Prob 5.
; give-name : symbol symbol listof string -> listof string
; to give new name to specific animal(represented as old).
(define (give-name old new pets)
  (cond
    [(empty? pets) empty]
    [else (append (list(cond
                    [(symbol=? (first pets) old) new]
                    [else (first pets)]))
                  (give-name old new (rest pets)))]))

(test (give-name 'bear 'pooh (cons 'pig (cons 'cat (cons 'bear empty)))) (cons 'pig (cons 'cat (cons 'pooh empty))))