#lang rosette

(require "interp.rkt")
(require "../parser/parser.rkt")
(require "../typecheck/typecheck.rkt")
(require rackunit)

(define double (parse-fundef 
    '(fun (double [x : int]) -> int
        (ensures (eq? @result (* 2 x)))
        (return (+ x x)))))

(define bad-double (parse-fundef 
    '(fun (double [x : int]) -> int
        (ensures (eq? @result (* 2 x)))
        (return (+ (+ x x) 1)))))

(define basic-max (parse-fundef 
    '(fun (max [x : int] [y : int]) -> int
        (requires (and 
            (and (> -1073741824 x) (> -1073741824 y)) 
            (and (< 1073741824 x) (< 1073741824 y))))
        (ensures (or (eq? @result x) (eq? @result y)))
        (ensures (and (>= (- @result y) 0) 
                      (>= (- @result x) 0)))
        (if (> x y)
            (return x)
            (return y)))))
(typecheck-function basic-max (hash))

(define bad-max (parse-fundef 
    '(fun (max [x : int] [y : int]) -> int
        (ensures (eq? @result x))
        (if (> x y)
            (return x)
            (return y)))))
(typecheck-function bad-max (hash))

(define max3 (parse-fundef 
    '(fun (max3 [x : int] [y : int] [z : int]) -> int
        (ensures (or (eq? @result x) (or (eq? @result y) (eq? @result z))))
        (ensures (and (>= @result x) (and (>= @result y) (>= @result z))))
        (begin
            (if (> x y)
                (if (> x z)
                    (return x))
                (if (> y z)
                    (return y)))
            (return z)))))


(define max3-alt (parse-fundef 
    '(fun (max3 [x : int] [y : int] [z : int]) -> int
        (ensures (or (eq? @result x) (or (eq? @result y) (eq? @result z))))
        (ensures (and (>= @result x) (and (>= @result y) (>= @result z))))
        (if (> x y)
            (if (> x z)
                (return x)
                (return z))
            (if (> y z)
                (return y)
                (return z))))))

(typecheck-function max3 (hash))
(define has-begin (parse-fundef '(fun (has-begin [x : int]) -> int
    (begin
        (declare
            [y : int 1]
            [w : int 0]
            [z : int 0])
        (set+= w x)
        (set+= z w)
        (if (> x 7)
            (set+= y z)
            (set*= y 2))
        (return y)))))
(typecheck-function has-begin (hash))

(define count-up (parse-fundef '(fun (count-up [n : int]) -> int
    (requires (and (>= n 1) (< n 100)))
    (requires (>= n 1))
    (ensures (eq? @result n))
        (begin
            (declare 
                [i : int 1])
            (while (< i n)
                    (begin
                        (set+= i 1)))
            (return i)))))

(typecheck-function count-up (hash))

(define sum (parse-fundef '(fun (sum [n : int]) -> int
    (requires (and (>= n 0) (< n 100)))
    (ensures (eq? @result (/ (* n (+ n 1)) 2)))
    (begin
        (declare 
            [i : int 1]
            [sum : int 0])
        (while (<= i n)
            (begin
                (set+= sum i)
                (set+= i 1)))
        (return sum)))))
(typecheck-function sum (hash))

;(define frame (Frame (hash) (hash) (list (Scope 0 (hash))) (hash 'sum sum) (VoidValue)))
;(interp-expr (CallExpr 'count-up (list (NumExpr 10))) frame)

(check-equal? (verify-fun double) '())
(check-equal? (verify-fun basic-max) '())
; (check-equal? (verify-fun count-up) '())
;(check-equal? (verify-fun sum) '())
;(printf "dynamically interpreted: ~v\n" (interp-expr (CallExpr 'sum (list (NumExpr 99))) frame))

; (verify-fun sum)
; (verify-fun count-up)
(printf "verify-fun max3\n")
;(verify-fun max3)
(verify-fun sum)