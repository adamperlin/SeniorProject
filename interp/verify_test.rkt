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
        (ensures (or (eq? @result x) (eq? @result y)))
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
        (ensures (or (eq? @result y) (eq? @result z)))
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
        (begin
            (declare 
                [i : int 1])
            (while (< i n)
                    (begin
                        (set+= i 1)))
            (return i)))))

(typecheck-function count-up (hash))

(define sum (parse-fundef '(fun (sum [n : int]) -> int
    (requires (>= n 0))
    (ensures (eq? @result (/ (* n (+ n 1)) 2)))
    (begin
        (declare 
            [i : int 1]
            [sum : int 0])
        (while (<= i n)
;            ((invariant (eq? sum (/ (* i (- i 1)) 2)))
            (begin
                (set+= sum i)
                (set+= i 1)))
        (return sum)))))
(typecheck-function sum (hash))
; (define frame (Frame (hash) (hash) (list (Scope 0 (hash))) (hash 'count-up count-up) (VoidValue)))
; (interp-expr (CallExpr 'count-up (list (NumExpr 10))) frame)

; (verify-fun double)
; (verify-fun bad-double)
; (verify-fun basic-max)
;(printf "verifying count-up\n")
;(verify-fun count-up)
(verify-fun sum)
; (verify-fun has-begin)

;(print double)
;(check-equal? (verify (verify-fun double)) (unsat))
; (check-not-equal? (verify (verify-fun bad-double)) (unsat))
; (check-equal? (verify (verify-fun basic-max)) (unsat))
; (check-not-equal? (verify (verify-fun bad-max)) (unsat))
; (verify (verify-fun max3))

; (define top-env (hash
;     'max3 max3))

; (define (new-frame-with-env env)
;   (Frame (make-hash) (make-hash) (cons (make-hash) '()) env (Value)))

; (define frame (new-frame-with-env top-env))
; (interp-expr (parse-expr '(max3 5 1 3)) frame)