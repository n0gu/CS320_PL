#lang plai

; Prob 1.
; yen->won: number -> number
; to change Japanese yens into won considering the exchange rate
; (in this case, 10)
(define (yen->won yen)
  (* 10 yen))
(test (yen->won 7) 70)

; Prob 2.
; is-multiple-eleven?: number -> boolean
; to determine whether n is multiple of 11
(define (is-multiple-eleven? n)
  (= (remainder n 11) 0))
(test (is-multiple-eleven? 22) true)

; Prob 3.
; area-triangle: number -> number
; to calculate area of triangle using base length and height
(define (area-triangle a b)
  (/ (* a b) 2))
(test (area-triangle 4 6) 12)

; Prob 4.
; max: number number number number number -> number
; to find maximum number among five numbers
(define (max a1 a2 a3 a4 a5)
  (cond
    [(and (>= a1 a2) (>= a1 a3) (>= a1 a4) (>= a1 a5) a1)]
    [(and (>= a2 a1) (>= a2 a3) (>= a2 a4) (>= a2 a5) a2)]
    [(and (>= a3 a1) (>= a3 a2) (>= a3 a4) (>= a3 a5) a3)]
    [(and (>= a4 a1) (>= a4 a2) (>= a4 a3) (>= a4 a5) a4)]
    [(and (>= a5 a1) (>= a5 a2) (>= a5 a4) (>= a5 a5) a5)]))
(test (max 15 8 6 1 8) 15)
(test (max 8 15 8 6 1) 15)
(test (max 8 1 15 8 6) 15)
(test (max 8 1 6 15 8) 15)
(test (max 8 1 6 8 15) 15)

; Prob 5.
; min: number number number number number -> number
; to find minimum number among five numbers
(define (min a1 a2 a3 a4 a5)
  (cond
    [(and (<= a1 a2) (<= a1 a3) (<= a1 a4) (<= a1 a5) a1)]
    [(and (<= a2 a1) (<= a2 a3) (<= a2 a4) (<= a2 a5) a2)]
    [(and (<= a3 a1) (<= a3 a2) (<= a3 a4) (<= a3 a5) a3)]
    [(and (<= a4 a1) (<= a4 a2) (<= a4 a3) (<= a4 a5) a4)]
    [(and (<= a5 a1) (<= a5 a2) (<= a5 a4) (<= a5 a5) a5)]))
(test (min 1 6 8 15 8) 1)
(test (min 6 1 8 15 8) 1)
(test (min 8 6 1 15 8) 1)
(test (min 8 6 8 1 8) 1)
(test (min 8 6 8 15 1) 1)