#lang racket

(require "interp.rkt")
(require "../parser/parser.rkt")
(require "../typecheck/typecheck.rkt")
(require rackunit)


(define make-int-value
    (compose IntValue int32))

(define frame (new-frame))
(check-equal? (set-local frame 'x (make-int-value 10)) (Frame (hash) (hash) (list (Scope 0 (hash 'x (Binding 0 (IntValue (int32 10)))))) (hash) (Value)))
(check-equal? (set-local (set-local frame 'x (make-int-value 10)) 'y (make-int-value 20)) 
    (Frame (hash) (hash) (list 
                                (Scope 0 (hash 'x (Binding 0 (IntValue (int32 10)))
                                      'y (Binding 0 (IntValue (int32 20)))))) (hash) (Value)))
(check-equal? (get-local (set-local frame 'x (make-int-value 10)) 'x) (make-int-value 10))

(define (frame-with-scope scope) 
    (push-scope (new-frame) scope))
    
(define (frame-with-ret frame ret) 
    (struct-copy Frame frame [return ret]))

(define decls 
    (list 
        (Decl 'x 'int (Some (BinOpExpr '* (NumExpr 2) (NumExpr 100))))
        (Decl 'y 'bool (Some (BinOpExpr 'and 'true 'false)))))

(check-equal? (eval-decls decls frame)
    (Frame (hash) (hash)  (list (Scope 0 (hash 'x (Binding 0 (make-int-value 200))
                                     'y (Binding 0 (BoolValue #f))))) (hash) (Value)))

; (define name-vals1 (eval-decls decls frame))

; (check-equal? (new-scope frame name-vals1)
;     (Frame (hash) (hash) (list 
;                                 (Scope 1
;                                     (hash 'x (Binding 1 (make-int-value 200))
;                                           'y (Binding 1 (BoolValue #f))))
;                                 (Scope 0 (hash))) (hash) (Value)))
; (define make-int-value
;     (compose IntValue int32))

(check-equal? (interp-expr (NumExpr 1) (new-frame)) (make-int-value 1))
(check-equal? (interp-expr (NumExpr -1000) (new-frame)) (make-int-value -1000))



;(define test-frame (Frame (make-hash) (make-hash) (list (hash 'a (box (make-int-value 3)) 'b (box (BoolValue #t)))) (make-hash) (make-int-value 0)))
(define test-frame (frame-with-scope 
    (Scope 1
        (hash 'a (Binding 1 (make-int-value 3)) 'b (Binding 1 (BoolValue #t))))))

;; simple expression tests

(check-equal? (interp-expr (IdExpr 'a) test-frame) (make-int-value 3))
(check-equal? (interp-expr (IdExpr 'b) test-frame) (BoolValue #t))
(check-equal? (interp-expr (BinOpExpr '+ (IdExpr 'a) (NumExpr 1)) test-frame) (make-int-value 4))
(check-equal? (interp-expr (BinOpExpr '<< (IdExpr 'a) (NumExpr 1)) test-frame) (make-int-value 6))
(check-equal? (interp-expr (BinOpExpr '>> (IdExpr 'a) (NumExpr 1)) test-frame) (make-int-value 1))
(check-equal? (interp-expr (BinOpExpr 'eq? (IdExpr 'a) (NumExpr 3)) test-frame) (BoolValue #t))
(check-equal? (interp-expr (UnOpExpr '~ (NumExpr 1024)) test-frame) (make-int-value -1025))
(check-equal? (interp-expr (BinOpExpr 'xor (NumExpr 8) (NumExpr 2)) test-frame) (make-int-value 10))
(check-equal? (interp-expr (BinOpExpr '* (IdExpr 'a) (NumExpr 10)) test-frame) (make-int-value 30))
(check-equal? (interp-expr (BinOpExpr '/ (NumExpr 30) (NumExpr 10)) test-frame) (make-int-value 3))
(check-equal? (interp-expr (BinOpExpr 'band (NumExpr 1) (NumExpr 0)) test-frame) (make-int-value 0))
(check-equal? (interp-expr (BinOpExpr 'bor (NumExpr 8) (NumExpr 1)) test-frame) (make-int-value 9))
(check-equal? (interp-expr (BinOpExpr 'and 'true 'true) test-frame) (BoolValue #t))
(check-equal? (interp-expr (BinOpExpr 'or 'true 'false) test-frame) (BoolValue #t))
(check-equal? (interp-expr (UnOpExpr '! 'true) test-frame) (BoolValue #f))
(check-equal? (interp-expr (UnOpExpr 'neg (NumExpr 10)) test-frame) (make-int-value -10))

; ; inc/dec tests
(define test-frame1  (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value 3)) 'b (Binding 1 (BoolValue #t))))))
(define want-frame1  (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value 4)) 'b (Binding 1 (BoolValue #t))))))
(define want-frame2 (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value 2)) 'b (Binding 1 (BoolValue #t))))))
(check-equal? (interp-stmt (IncStmt 'a) test-frame1) (cons 'continue want-frame1))
(check-equal? (interp-stmt (DecStmt 'a) test-frame1) (cons 'continue want-frame2))

; ; assignment tests
(define test-frame2 (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value 3)) 
                                        'b (Binding 1 (BoolValue #t))))))

(check-equal? (interp-stmt (AssignStmt 'set+= 'a (NumExpr 10)) test-frame2) 
    (cons 'continue 
        (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value 13)) 
                                        'b (Binding 1 (BoolValue #t)))))))


(check-equal? (interp-stmt (AssignStmt 'set<<= 'a (NumExpr 3)) test-frame2) (cons 'continue 
        (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value 24)) 
                                        'b (Binding 1 (BoolValue #t)))))))

(check-equal? (interp-stmt (AssignStmt 'set>>= 'a (NumExpr 1)) test-frame2) 
                    (cons 'continue (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value 1)) 
                                                    'b (Binding 1 (BoolValue #t)))))))

(check-equal? (interp-stmt (AssignStmt 'set= 'b 'false) test-frame2) 
                                (cons 'continue (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value 3)) 
                                                    'b (Binding 1 (BoolValue #f)))))))

(check-equal? (interp-stmt (IfStmt (BinOpExpr '>= (IdExpr 'a) (NumExpr 0)) 
                            (AssignStmt 'set= 'a (NumExpr -2))
                            (Some (AssignStmt 'set= 'a (NumExpr -3)))) test-frame2) 

                            (cons 'continue (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value -2)) 
                                                    'b (Binding 1 (BoolValue #t)))))))

(check-equal? (interp-stmt (IfStmt (UnOpExpr '! (IdExpr 'b))
                            (AssignStmt 'set= 'a (NumExpr -2))
                            (Some (AssignStmt 'set= 'a (NumExpr -3)))) test-frame2) 
                                (cons 'continue (frame-with-scope (Scope 1 (hash 'a (Binding 1 (make-int-value -3)) 
                                                    'b (Binding 1 (BoolValue #t)))))))

;; ret
(check-equal? (interp-stmt (RetStmt (Some (NumExpr -234))) (new-frame)) 
                (cons 'return (frame-with-ret (new-frame) (make-int-value -234))))


(define test-frame3  
        (frame-with-scope (Scope 1 (hash 'i (Binding 1 (make-int-value 0)) 
              'sum (Binding 1 (make-int-value 0))))))

(check-equal? (interp-stmt 
                    (WhileStmt (BinOpExpr '< (IdExpr 'i) (NumExpr '10)) 
                        (IncStmt 'i)) test-frame3) 
                        (cons 'continue
                            (frame-with-scope (Scope 1 (hash 'i (Binding 1 (make-int-value 10)) 
                            'sum (Binding 1 (make-int-value 0)))))))

(define test-frame4  
        (frame-with-scope 
            (Scope 1 (hash 'i (Binding 1 (make-int-value 0)) 
              'sum (Binding 1 (make-int-value 0))))))

(check-equal? (interp-stmt 
                    (WhileStmt (BinOpExpr '< (IdExpr 'i) (NumExpr '10)) 
                        (IfStmt (BinOpExpr 'eq? (IdExpr 'i) (NumExpr 5))
                            (RetStmt (Some (IdExpr 'i)))
                            (Some (IncStmt 'i)))) test-frame4) 
                    (cons 'return
                        (frame-with-ret (frame-with-scope 
                            (Scope 1 (hash 'i (Binding 1 (make-int-value 5)) 
                            'sum (Binding 1 (make-int-value 0))))) (make-int-value 5))))

(define test-frame5
        (frame-with-scope 
            (Scope 1 (hash 'i (Binding 1 (make-int-value 0)) 
              'sum (Binding 1 (make-int-value 0))))))

; (define test-frame5 (Frame (make-hash) (make-hash) 
;     (list 
;         (hash 'i (box (make-int-value 0)) 
;               'sum (box (make-int-value 0))))
;     (make-hash) 
;     (make-int-value 0)))

;(define init-scope (Scope 1 (hash 'i (make-int-value 0))))

; (interp-stmt
;             (BeginStmt (list (Decl 'i 'int (None)) (Decl 'b 'bool (Some 'false)))
;                 (list (AssignStmt 'set+= 'i (NumExpr 1)) (AssignStmt 'set= 'b 'true))) test-frame5) 
(check-equal? (interp-stmt
            (BeginStmt (list (Decl 'i 'int (None)) (Decl 'b 'bool (Some 'false)))
                (list (AssignStmt 'set+= 'i (NumExpr 1)) (AssignStmt 'set= 'b 'true))) test-frame5) 
                (cons 'continue (frame-with-scope (Scope 1 (hash 'i (Binding 1 (make-int-value 0)) 'sum (Binding 1 (make-int-value 0)))))))


(check-equal? (interp-stmt
                (parse-stmt '(begin 
                                (set+= i 10)
                                (set= sum (bor sum 1)))) test-frame5)
                (cons 'continue (frame-with-scope (Scope 1 (hash 'i (Binding 1 (make-int-value 10)) 'sum (Binding 1 (make-int-value 1)))))))

(check-equal? (interp-stmt (BeginStmt (list (Decl 'x 'int (Some (NumExpr 2))) (Decl 'b 'bool (Some 'true)))
     (list (IfStmt (IdExpr 'b) (AssignStmt 'set+= 'i (IdExpr 'x)) (None)))) test-frame5)
     (cons 'continue 
        (frame-with-scope 
            (Scope 1 
                (hash 
                    'i (Binding 1 (make-int-value 2)) 
                    'sum (Binding 1 (make-int-value 0)))))))


(define test-frame6 (new-frame))
(check-equal? (interp-stmt (parse-stmt '(begin 
    (declare 
        [i : int 10]
        [j : int 20])
    (if (< i j)
        (set= i j))
    (set= i (+ i 1))
    (return i))) test-frame6) 
    (cons 'return (frame-with-ret (new-frame) (make-int-value 21))))

; (define big-def-ast (Fundef 'sum (list (Decl 'n 'int (None))) 'int
;     (list 
;         (Contract 'requires (BinOpExpr '>= (IdExpr 'n) (NumExpr 0))))
;     (list
;         (Contract 'ensures (BinOpExpr 'eq?
;                             '@result
;                                 (BinOpExpr '/ 
;                                     (BinOpExpr '*
;                                         (IdExpr 'n)
;                                         (BinOpExpr '+
;                                             (IdExpr 'n)
;                                             (NumExpr 1)))
;                                 (NumExpr 2)))))
;     (BeginStmt
;         (list
;             (Decl 'i 'int (Some (NumExpr 1)))
;             (Decl 'sum 'int (Some (NumExpr 0))))
;         (list
;             (WhileStmt (BinOpExpr '<= (IdExpr 'i) (IdExpr 'n))
;                 (AnnoStmt
;                     (list
;                         (Anno 'invariant (BinOpExpr 'eq?
;                                 (IdExpr 'sum)
;                                     (BinOpExpr '/ 
;                                         (BinOpExpr '*
;                                             (IdExpr 'i)
;                                             (BinOpExpr '-
;                                                 (IdExpr 'i)
;                                                 (NumExpr 1)))
;                                     (NumExpr 2)))))
;                         (BeginStmt
;                             '()
;                             (list (AssignStmt 'set+= 'sum (IdExpr 'i))
;                                 (AssignStmt 'set+= 'i (NumExpr 1))))))))))

(define sum (parse-fundef '(fun (sum [n : int]) -> int
    (requires (>= n 0))
    (ensures (eq? @result (/ (* n (+ n 1)) 2)))
    (begin
        (declare 
            [i : int 1]
            [sum : int 0])
        (while (<= i n)
            ((invariant (eq? sum (/ (* i (- i 1)) 2)))
                (begin
                    (set+= sum i)
                    (set+= i 1))))
        (return sum)))))

(define  max-fun (parse-fundef '(fun (max [x : int] [y : int]) -> int
    (if (> x y)
        (return x)
        (return y)))))

(define no-args (parse-fundef 
    '(fun (f) -> int
        (begin
            (if (< 3 4)
                (begin
                (declare
                    [a : int 10]
                    [z : int 20])
                    (return (+ a z))))
                (return 2)))))

(define fact 
     (parse-fundef '(fun (fact [n : int]) -> int
            (if (eq? n 0)
                (return 1)
                (return (* n (fact (- n 1))))))))

(define f
    (parse-fundef '(fun (f [x : int]) -> int (return (+ x 10)))))

(define g
    (parse-fundef '(fun (g [y : int]) -> int (return (- y 1)))))

(define e 
    (parse-fundef '(fun (e [x : int]) -> int (return (<< x 2)))))

(define h (parse-fundef '(fun (h [x : int]) -> int
    (return (e (+ (g x) (f x)))))))

(define has-contract (parse-fundef '(fun (has-contract [x : int]) -> int
    (requires (> x 0))
    (ensures (> @result 0))
    (return (+ x 1))
)))

(define breaks-ensures (parse-fundef '(fun (breaks-ensures [x : int]) -> int
    (requires (> x 0))
    (ensures (> @result 0))
    (return (- x 1))
)))


(define gcd (parse-fundef '(fun (gcd [a : int] [b : int]) -> int
    (begin
        (declare 
            [r : int (% a b)])
        (while (> r 0)
            (begin
                (set= a b)
                (set= b r)
                (set= r (% a b))))
        (return b)))))

(define count-up (parse-fundef '(fun (count-up [n : int]) -> int
        (begin
            (declare 
                [i : int 1])
            (while (< i n)
                    (begin
                        (set+= i 1)))
            (return i)))))

; ; function calls
(define test-env (hash
    'max max-fun
    'no-args no-args
    'fact fact
    'f f
     'g g
     'h h
     'e e
     'sum sum
     'gcd gcd
     'count-up count-up
    'has-contract has-contract
    'breaks-ensures breaks-ensures))

(define test-frame7 (new-frame test-env))
(check-equal? (interp-expr (CallExpr 'max (list (NumExpr 3) (NumExpr 4))) test-frame7) (make-int-value 4))
(check-equal? (interp-expr (CallExpr 'no-args '()) test-frame7) (make-int-value 30))
(check-equal? (interp-expr (CallExpr 'fact (list (NumExpr 10))) test-frame7) (make-int-value 3628800))
(check-equal? (interp-expr (CallExpr 'h (list (NumExpr 3))) test-frame7) (make-int-value 60))
(check-equal? (interp-expr (CallExpr 'gcd (list (NumExpr 35) (NumExpr 14))) test-frame7) (make-int-value 7))

; basic contract testing
(check-equal? (interp-expr (CallExpr 'has-contract (list (NumExpr 1))) test-frame7) (make-int-value 2))
(check-exn (regexp (regexp-quote "requires: contract check failed"))
    (lambda ()
        (interp-expr (CallExpr 'has-contract (list (NumExpr 0))) test-frame7)))

(check-exn (regexp (regexp-quote "ensures: contract check failed"))
    (lambda ()
        (interp-expr (CallExpr 'breaks-ensures (list (NumExpr 1))) test-frame7)))

(check-equal? (interp-expr (CallExpr 'sum (list (NumExpr 12))) test-frame7) (make-int-value 78))

(define prog (list
    max-fun 
    (parse-fundef '(fun (main) 
        (return (max 5 6))))))
(check-equal? (interp-prog prog) (make-int-value 6))

(define prog1 '(
    (fun (gcd [a : int] [b : int]) -> int
        (begin
            (declare 
                [r : int (% a b)])
            (while (> r 0)
                (begin
                    (set= a b)
                    (set= b r)
                    (set= r (% a b))))
            (return b)))
    
    (fun (sum [n : int]) -> int
        (requires (>= n 0))
        (ensures (eq? @result (/ (* n (+ n 1)) 2)))
        (begin
            (declare 
                [i : int 1]
                [sum : int 0])
            (while (<= i n)
                ((invariant (eq? sum (/ (* i (- i 1)) 2)))
                    (begin
                        (set+= sum i)
                        (set+= i 1))))
            (return sum)))
    (fun (main) -> bool
        (begin
            (declare
                [x : int (gcd 100 80)]
                [y : int (sum x)])
            (if (eq? (/ y x) 10)
                (return true)
                (return false))))))

(check-equal? (top-interp prog1) (BoolValue #t))

; testing annotations
(check-equal? (car (interp-stmt (parse-stmt '(begin 
    (declare
        [var : bool false]
        [x : int 10])
    ((assert true)
     (assert (> x 0))
     (set= x 10)))) test-frame7)) 'continue)
    
(check-exn (regexp (regexp-quote "validation failed")) (lambda () 
    (interp-stmt (parse-stmt '(begin 
        (declare
            [var : bool false]
            [x : int 10])
        ((assert var)
        (assert (< x 0))
        (set= x 10)))) test-frame7)))
    

(check-exn (regexp (regexp-quote "validation failed")) (lambda () 
    (interp-stmt (parse-stmt '(begin 
        (declare
            [i : int 0]
            [x : int 10])
        (while (< i x)
        ((invariant (< i (- x 1)))
        (set+= i 1))))) test-frame7)))

(define test-frame8 (Frame 
    (hash)
    (hash
        'x (make-int-value 10))
    '()
    test-env
    (VoidValue)))

(check-equal? (interp-expr (OldExpr (IdExpr 'x)) test-frame8) (make-int-value 10))
(check-equal? (interp-expr (OldExpr (BinOpExpr '+ (NumExpr 20) (IdExpr 'x))) test-frame8) (make-int-value 30))

;; tests of loop bounding behavior


(check-equal? (interp-expr (CallExpr 'count-up (list (NumExpr (depth-limit)))) (new-frame test-env))
        (make-int-value 100))

(check-exn
    (regexp (regexp-quote "loop depth exceeded"))
    (λ () (interp-expr (CallExpr 'count-up (list (NumExpr (add1 (depth-limit))))) (new-frame test-env))))