#lang plai

; a - basic "call a2 to add 2, call a3 to add 3" method
; b - "call b2 with ... to add 2, and so on" - state saving
; c - b plus 'various type input'
; those three are skipped

; d, e - continuous read call
(define (d)
  (do-d 0))
(define (do-d total)
  (begin
    (printf "Total is ~a\nAdd 2 next?\n" total)
    (do-d (+ total
             (if (read) 2 3)))))
 
(define (e)
  (do-e 0))
(define (num-read prompt)
  (begin
    (printf "~a\n" prompt)
    (read)))
(define (do-e total)
  (do-e (+ (num-read
            (format "Total is ~a\nNext number...\n" total))
           total)))



; f - "web-read" method, which is not specific to f
; difference with a, b, and c is that actual "adding" process in f is passed as an argument,
; while in abc, those process are in a2, a3, b2, etc.
(define table empty)
(define (remember v)
  (local [(define n (length table))]
    (begin (set! table (append table (list v)))
           n)))
(define (lookup key)
  (list-ref table key))

(define (f)
  (do-f 0))
(define (web-read/k prompt cont)
  (local [(define key (remember cont))]
    `(,prompt "To continue, call resume/k with " ,key " and value")))
(define (resume/k key val)
  (local [(define cont (lookup key))]
    (cont val))) ;((first l) (+ (second l) val))
(define (do-f total)
  (web-read/k
   (format "Total is ~a\nNext number?" total)
   (lambda (val)
     (do-f (+ total val)))))


   
; g - how do we call it twice? we cannot use "begin"...
(define (g1)
  (+ (num-read "First number")
     (num-read "Second number")))
(define (h1)
  (begin (g1) (g1)))
(define (g2)
  (web-read/k "First number"
              (lambda (v1)
                (web-read/k "Second number"
                            (lambda (v2)
                              (+ v1 v2))))))
(define (h2)
  (begin (g2) (g2))) ;first call works behind, so we can't see



(define (identity x) x)

(define (g) (do-g identity))
(define (do-g cont)
  (web-read/k "First number"
              (lambda (v1)
                (web-read/k "Second number"
                            (lambda (v2)
                              (cont (+ v1 v2)))))))
(define (web-pause/k prompt cont)
  (local [(define key (remember cont))]
    `(,prompt "To continue, call p-resume/k with " ,key)))
(define (p-resume/k key)
  (local [(define cont (lookup key))]
    (cont)))
(define (h) (do-h identity)) ;work g twice
(define (do-h cont)
  (do-g (lambda (sum)
          (web-pause/k sum
                       (lambda () (do-g cont))))))

