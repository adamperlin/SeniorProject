#lang racket

(require "interp/interp.rkt")


(define prog 
    '((fun (sum [n : int]) -> int
        (requires (>= n 10))
        (ensures (eq? @result (/ (* n (+ n 1)) 2)))
        (begin
            (declare 
                [i : int 0]
                [sum : int 0])
            (while (<= i n)
                ((invariant (eq? sum (/ (* i (- i 1)) 2)))
                    (begin
                        (set+= sum i)
                        (set+= i 1))))
            (return sum)))
        (fun (main) -> int
            (return (sum 10)))))

(print (top-interp prog))


