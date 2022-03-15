#lang racket

(require "interp.rkt")
(require "../parser/parser.rkt")
(require "../typecheck/typecheck.rkt")
(require rackunit)

(check-equal? (interp-expr (NumExpr 1) (new-frame)) (IntValue 1))
(check-equal? (interp-expr (NumExpr -1000) (new-frame)) (IntValue -1000))

(define test-frame (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue 3)) 'b (box (BoolValue #t)))) (make-hash) (IntValue 0)))


; simple expression tests

(check-equal? (interp-expr (IdExpr 'a) test-frame) (IntValue 3))
(check-equal? (interp-expr (IdExpr 'b) test-frame) (BoolValue #t))
(check-equal? (interp-expr (BinOpExpr '+ (IdExpr 'a) (NumExpr 1)) test-frame) (IntValue 4))
(check-equal? (interp-expr (BinOpExpr '<< (IdExpr 'a) (NumExpr 1)) test-frame) (IntValue 6))
(check-equal? (interp-expr (BinOpExpr '>> (IdExpr 'a) (NumExpr 1)) test-frame) (IntValue 1))
(check-equal? (interp-expr (BinOpExpr 'eq? (IdExpr 'a) (NumExpr 3)) test-frame) (BoolValue #t))
(check-equal? (interp-expr (UnOpExpr '~ (NumExpr 1024)) test-frame) (IntValue -1025))
(check-equal? (interp-expr (BinOpExpr 'xor (NumExpr 8) (NumExpr 2)) test-frame) (IntValue 10))
(check-equal? (interp-expr (BinOpExpr '* (IdExpr 'a) (NumExpr 10)) test-frame) (IntValue 30))
(check-equal? (interp-expr (BinOpExpr '/ (NumExpr 30) (NumExpr 10)) test-frame) (IntValue 3))
(check-equal? (interp-expr (BinOpExpr 'band (NumExpr 1) (NumExpr 0)) test-frame) (IntValue 0))
(check-equal? (interp-expr (BinOpExpr 'bor (NumExpr 8) (NumExpr 1)) test-frame) (IntValue 9))
(check-equal? (interp-expr (BinOpExpr 'and 'true 'true) test-frame) (BoolValue #t))
(check-equal? (interp-expr (BinOpExpr 'or 'true 'false) test-frame) (BoolValue #t))
(check-equal? (interp-expr (UnOpExpr '! 'true) test-frame) (BoolValue #f))
(check-equal? (interp-expr (UnOpExpr 'neg (NumExpr 10)) test-frame) (IntValue -10))

; inc/dec tests
(define test-frame1 (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue 3)) 'b (box (BoolValue #t)))) (make-hash) (IntValue 0)))
(check-equal? (interp-stmt (IncStmt 'a) test-frame1) 'continue)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue 4)) 'b (box (BoolValue #t)))) (make-hash) (IntValue 0)) test-frame1)
(check-equal? (interp-stmt (DecStmt 'a) test-frame1) 'continue)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue 3)) 'b (box (BoolValue #t)))) (make-hash) (IntValue 0)) test-frame1)

; assignment tests
(define test-frame2 (Frame (make-hash) (make-hash)
    (list 
        (hash 'a (box (IntValue 3)) 
              'b (box (BoolValue #t))))
    (make-hash) 
    (IntValue 0)))

(check-equal? (interp-stmt (AssignStmt 'set+= 'a (NumExpr 10)) test-frame2) 'continue)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue 13)) 'b (box (BoolValue #t)))) (make-hash) (IntValue 0)) test-frame2)

(check-equal? (interp-stmt (AssignStmt 'set<<= 'a (NumExpr 3)) test-frame2) 'continue)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue 104)) 'b (box (BoolValue #t)))) (make-hash) (IntValue 0)) test-frame2)

(check-equal? (interp-stmt (AssignStmt 'set>>= 'a (NumExpr 1)) test-frame2) 'continue)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue 52)) 'b (box (BoolValue #t)))) (make-hash) (IntValue 0)) test-frame2)

(check-equal? (interp-stmt (AssignStmt 'set= 'b 'false) test-frame2) 'continue)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue 52)) 'b (box (BoolValue #f)))) (make-hash) (IntValue 0)) test-frame2)


(check-equal? (interp-stmt (IfStmt (BinOpExpr '>= (IdExpr 'a) (NumExpr 0)) 
                            (AssignStmt 'set= 'a (NumExpr -2))
                            (Some (AssignStmt 'set= 'a (NumExpr -3)))) test-frame2) 'continue)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue -2)) 'b (box (BoolValue #f)))) (make-hash) (IntValue 0)) test-frame2)

(check-equal? (interp-stmt (IfStmt (IdExpr 'b)
                            (AssignStmt 'set= 'a (NumExpr -2))
                            (Some (AssignStmt 'set= 'a (NumExpr -3)))) test-frame2) 'continue)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue -3)) 'b (box (BoolValue #f)))) (make-hash) (IntValue 0)) test-frame2)

; ret
(check-equal? (interp-stmt (RetStmt (Some (NumExpr -234))) test-frame2) 'return)
(check-equal? (Frame (make-hash) (make-hash) (list (hash 'a (box (IntValue -3)) 'b (box (BoolValue #f)))) (make-hash) (IntValue -234)) test-frame2)


(define test-frame3 (Frame (make-hash) (make-hash) 
    (list 
        (hash 'i (box (IntValue 0)) 
              'sum (box (IntValue 0))))
    (make-hash) 
    (IntValue 0)))

(check-equal? (interp-stmt 
                    (WhileStmt (BinOpExpr '< (IdExpr 'i) (NumExpr '10)) 
                        (IncStmt 'i)) test-frame3) 'continue)

(check-equal? (Frame (make-hash) (make-hash) (list (hash 'i (box (IntValue 10)) 'sum (box (IntValue 0)))) (make-hash) (IntValue 0)) test-frame3)

(define test-frame4 (Frame (make-hash) (make-hash) 
    (list 
        (hash 'i (box (IntValue 0)) 
              'sum (box (IntValue 0))))
    (make-hash) 
    (IntValue 0)))
(check-equal? (interp-stmt 
                    (WhileStmt (BinOpExpr '< (IdExpr 'i) (NumExpr '10)) 
                        (IfStmt (BinOpExpr 'eq? (IdExpr 'i) (NumExpr 5))
                            (RetStmt (Some (IdExpr 'i)))
                            (Some (IncStmt 'i)))) test-frame4) 'return)

(check-equal? test-frame4 (Frame (make-hash) (make-hash) 
                        (list 
                            (hash 'i (box (IntValue 5)) 
                                'sum (box (IntValue 0))))
                        (make-hash) 
                        (IntValue 5)))

(define test-frame5 (Frame (make-hash) (make-hash) 
    (list 
        (hash 'i (box (IntValue 0)) 
              'sum (box (IntValue 0))))
    (make-hash) 
    (IntValue 0)))

(check-equal? (interp-stmt (BeginStmt (list (Decl 'i 'int (None)) (Decl 'b 'bool (Some 'false)))
    (list (AssignStmt 'set+= 'i (NumExpr 1)) (AssignStmt 'set= 'b 'true))) test-frame5) 'continue)
(check-equal? test-frame5 (Frame (make-hash) (make-hash)
    (list 
        (hash 'i (box (IntValue 0)) 
              'sum (box (IntValue 0))))
    (make-hash)
    (IntValue 0)))

(check-equal? (interp-stmt (BeginStmt (list (Decl 'x 'int (Some (NumExpr 2))) (Decl 'b 'bool (Some 'true)))
    (list (IfStmt (IdExpr 'b) (AssignStmt 'set+= 'i (IdExpr 'x)) (None)))) test-frame5) 'continue)

(check-equal? test-frame5 (Frame (make-hash) (make-hash) 
    (list 
        (hash 'i (box (IntValue 2)) 
              'sum (box (IntValue 0))))
        (make-hash) 
    (IntValue 0)))

(define test-frame6 (new-frame))
(check-equal? (interp-stmt (parse-stmt '(begin 
    (declare 
        [i : int 10]
        [j : int 20])
    (if (< i j)
        (set= i j))
    (set= i (+ i 1))
    (return i))) test-frame6) 'return)

(check-equal? test-frame6 (Frame (make-hash) (make-hash)  (list (make-hash)) (make-hash) (IntValue 21)))

(define big-def-ast (Fundef 'sum (list (Decl 'n 'int (None))) 'int
    (list 
        (Contract 'requires (BinOpExpr '>= (IdExpr 'n) (NumExpr 0))))
    (list
        (Contract 'ensures (BinOpExpr 'eq?
                            '@result
                                (BinOpExpr '/ 
                                    (BinOpExpr '*
                                        (IdExpr 'n)
                                        (BinOpExpr '+
                                            (IdExpr 'n)
                                            (NumExpr 1)))
                                (NumExpr 2)))))
    (BeginStmt
        (list
            (Decl 'i 'int (Some (NumExpr 1)))
            (Decl 'sum 'int (Some (NumExpr 0))))
        (list
            (WhileStmt (BinOpExpr '<= (IdExpr 'i) (IdExpr 'n))
                (AnnoStmt
                    (list
                        (Anno 'invariant (BinOpExpr 'eq?
                                (IdExpr 'sum)
                                    (BinOpExpr '/ 
                                        (BinOpExpr '*
                                            (IdExpr 'i)
                                            (BinOpExpr '-
                                                (IdExpr 'i)
                                                (NumExpr 1)))
                                    (NumExpr 2)))))
                        (BeginStmt
                            '()
                            (list (AssignStmt 'set+= 'sum (IdExpr 'i))
                                (AssignStmt 'set+= 'i (NumExpr 1))))))))))

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

(define simple-fun (parse-fundef '(fun (max [x : int] [y : int]) -> int
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
(check-equal? (typecheck-function gcd) (void))

; function calls
(define test-env (make-hash (list 
    (cons 'max simple-fun)
    (cons 'no-args no-args)
    (cons 'fact fact)
    (cons 'f f)
    (cons 'g g)
    (cons 'h h)
    (cons 'e e)
    (cons 'sum sum)
    (cons 'gcd gcd)
    (cons  'has-contract has-contract)
    (cons  'breaks-ensures breaks-ensures))))

(define test-frame7 (Frame (make-hash) (make-hash) (list (make-hash)) test-env (IntValue 0)))
(check-equal? (interp-expr (CallExpr 'max (list (NumExpr 3) (NumExpr 4))) test-frame7) (IntValue 4))
(check-equal? (interp-expr (CallExpr 'no-args '()) test-frame7) (IntValue 30))
(check-equal? (interp-expr (CallExpr 'fact (list (NumExpr 10))) test-frame7) (IntValue 3628800))
(check-equal? (interp-expr (CallExpr 'h (list (NumExpr 3))) test-frame7) (IntValue 60))
(check-equal? (interp-expr (CallExpr 'gcd (list (NumExpr 35) (NumExpr 14))) test-frame7) (IntValue 7))



; basic contract testing
(check-equal? (interp-expr (CallExpr 'has-contract (list (NumExpr 1))) test-frame7) (IntValue 2))
(check-exn (regexp (regexp-quote "requires: contract check failed"))
    (lambda ()
        (interp-expr (CallExpr 'has-contract (list (NumExpr 0))) test-frame7)))

(check-exn (regexp (regexp-quote "ensures: contract check failed"))
    (lambda ()
        (interp-expr (CallExpr 'breaks-ensures (list (NumExpr 1))) test-frame7)))

(check-equal? (interp-expr (CallExpr 'sum (list (NumExpr 12))) test-frame7) (IntValue 78))

(define prog (list
    simple-fun
    (parse-fundef '(fun (main) 
        (return (max 5 6))))))
(check-equal? (interp-prog prog) (IntValue 6))

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
(check-equal? (interp-stmt (parse-stmt '(begin 
    (declare
        [var : bool false]
        [x : int 10])
    ((assert true)
     (assert (> x 0))
     (set= x 10)))) test-frame7) 'continue)
    
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

(define test-frame8 (Frame (make-hash) 
    (make-hash
        (list (cons 'x (box (IntValue 10)))))
    (list (make-hash
        (list (cons 'x (box (IntValue 10))))))
    test-env
    (VoidValue)))
(check-equal? (interp-expr (OldExpr (IdExpr 'x)) test-frame8) (IntValue 10))

(check-equal? test-frame8 (Frame (make-hash) 
    (make-hash
        (list (cons 'x (box (IntValue 10)))))
    (list (make-hash
        (list (cons 'x (box (IntValue 10))))))
    test-env
    (VoidValue)))