#lang typed/racket

(require typed/rackunit)
(require "typecheck.rkt")
(require "../parser/parser.rkt")

; expression typechecking tests
(define test-env (hash 'a 'int 'b 'bool))
(check-equal? (typecheck-expr (IdExpr 'a) test-env) 'int)
(check-exn (regexp (regexp-quote "unknown identifier 'c")) (lambda ()
    (typecheck-expr (IdExpr 'c) test-env)))

(check-equal? (typecheck-expr (NumExpr 3) test-env) 'int)
(check-equal? (typecheck-expr 'true test-env) 'bool)
(check-equal? (typecheck-expr 'false test-env) 'bool)

; binop tests
(check-equal? 
    (typecheck-expr (BinOpExpr '- 
        (IdExpr 'a) (NumExpr 2)) test-env) 'int)

(check-exn (regexp (regexp-quote "bad operand type for '>>: 'bool 'int"))
    (lambda () (typecheck-expr (BinOpExpr '>> (IdExpr 'b) (NumExpr 2)) test-env)))

;unop tests
(check-equal? 
    (typecheck-expr (UnOpExpr '!
        (IdExpr 'b)) test-env) 'bool)

(check-exn (regexp (regexp-quote "bad operand type for 'neg: 'bool")) 
    (lambda () (typecheck-expr (UnOpExpr 'neg (IdExpr 'b)) test-env)))

; assignment statement tests
(check-equal? (typecheck-stmt
        (AssignStmt 'set= 'a (NumExpr 5)) test-env) (void))

(check-exn (regexp (regexp-quote "assignment type mismatch: 'set= 'int 'bool"))
    (lambda () (typecheck-stmt (AssignStmt 'set= 'a 'true) test-env)))

(check-equal? (typecheck-stmt
        (AssignStmt 'set*= 'a (NumExpr 5)) test-env) (void))
    
(check-exn (regexp (regexp-quote "assignment type mismatch: 'set>>= 'int 'bool"))
    (lambda () (typecheck-stmt (AssignStmt 'set>>= 'a 'true) test-env)))

(check-equal? (typecheck-stmt
    (parse-stmt
        '(if true (set+= a 3) (set= b false))) test-env) (void))

(check-exn (regexp (regexp-quote "assignment type mismatch: 'set= 'bool 'int")) 
    (lambda () (typecheck-stmt
        (parse-stmt
            '(if true (set+= a 3) (set= b -1))) test-env) (void)))

(check-exn (regexp (regexp-quote "expecting if condition to be bool in (NumExpr 3)"))
    (lambda () (typecheck-stmt (parse-stmt '(if 3 (set+= a 2) (set+= b true))) test-env)))

(check-equal? (typecheck-stmt (parse-stmt 
        '(while (< a 5) (set+= a 1))) test-env) (void))

(check-exn (regexp (regexp-quote "expecting while condition to be bool"))
    (lambda () (typecheck-stmt (parse-stmt 
        '(while (>> a 1) (set= b false))) test-env)))

(check-equal? (typecheck-stmt (parse-stmt '(inc a)) test-env) (void))
(check-equal? (typecheck-stmt (parse-stmt '(dec a)) test-env) (void))

(check-exn (regexp (regexp-quote "cannot use operator dec on type 'bool in (DecStmt 'b)"))
    (lambda () (typecheck-stmt (parse-stmt '(dec b)) test-env)))

(check-exn (regexp (regexp-quote "cannot use operator inc on type 'bool in (IncStmt 'b)"))
    (lambda () (typecheck-stmt (parse-stmt '(inc b)) test-env)))

(check-equal? 
    (typecheck-stmt (parse-stmt '(begin 
        (set+= a 2)
        (set= b false))) test-env ) (void))

(check-equal? (typecheck-stmt 
    (parse-stmt '(begin 
        (declare
            [num : int 0]
            [isTrue : bool false])
        (set= num 10)
        (if isTrue (set*= num 2)))) test-env) (void))


(check-exn (regexp (regexp-quote "assignment type mismatch: 'set*= 'bool 'int"))
    (lambda ()
        (typecheck-stmt 
            (parse-stmt '(begin 
                (declare
                    [num : int 0]
                    [isTrue : bool false])
                (set= num 10)
                (if isTrue (set*= isTrue 2)))) test-env)))


(check-exn (regexp (regexp-quote "unknown identifier 'num"))
    (lambda ()
        (typecheck-stmt 
            (parse-stmt '(begin 
                (begin
                    (declare
                        [num : int 0]
                        [isTrue : bool false])
                    (set= num 10)
                    (if isTrue (set*= num 2))) (set+= num 1))) test-env)))



(check-exn (regexp (regexp-quote "'set+= 'bool 'int")) 
    (lambda () (typecheck-stmt 
        (parse-stmt '(begin 
            (declare 
                [num : bool true])
            (begin
                (declare
                    [num : int 0]
                    [isTrue : bool false])
                (set= num 10)
                (if isTrue (set*= num 2))) (set+= num 1))) test-env)))

(check-exn (regexp (regexp-quote "bad-annotation")) 
    (lambda () (typecheck-stmt
        (parse-stmt '((assert (+ 2 2))
                        (begin
                            (set= x 3)))) test-env)))

(define bad-contract '(fun (add1 [x : int]) -> int
                        (requires (+ x 2))
                        (return (+ x 1))))

(check-exn (regexp (regexp-quote "bad-contract"))
    (lambda () (typecheck-function (parse-fundef bad-contract) (hash)))) 

(define test-fn '(fun (max [a : int] [b : int]) -> int 
    (if (> a b)
        (return a)
        (return b))))

(check-equal? (typecheck-function (parse-fundef '(fun (max [a : int] [b : int]) -> int 
    (if (> a b)
        (return a)
        (return b)))) (hash)) (hash 'max (FunType '(int int) 'int)))

(check-exn (regexp (regexp-quote "cannot return type 'int from function of type 'void"))
    (lambda () (typecheck-function (parse-fundef '(fun (max [a : int] [b : int]) 
                (if (> a b)
                    (return a)
                    (return b)))) (hash))))

(define big-def '(fun (sum [n : int]) -> int
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
        (return sum))))

(check-equal? (typecheck-function (parse-fundef big-def) (hash)) (hash 'sum (FunType '(int) 'int)))

(check-equal? (check-return-paths (parse-fundef 
    '(fun (f [x : int]) -> int
        (return 10)))) (void))


(check-exn (regexp (regexp-quote "incomplete return paths"))
    (lambda () (check-return-paths (parse-fundef 
        '(fun (f [x : int]) -> int
            (set+= x 10))))))

(check-exn (regexp (regexp-quote "incomplete return paths"))
    (lambda () (check-return-paths (parse-fundef 
        '(fun (f [x : int]) -> int
            (if (< x 10) (return x)))))))


(check-equal? (check-return-paths 
    (parse-fundef 
            '(fun (f [x : int]) -> int
                (if (< x 10) (return x) (return (* x (/ x 2))))))) (void))

(check-exn (regexp (regexp-quote "incomplete return paths"))
    (lambda ()
        (check-return-paths (parse-fundef '(fun (f [y : int]) -> int
                    (if (< y 10)
                        (return 20)
                        (if (< y 2)
                            (return 30))))))))

(check-equal? (check-return-paths (parse-fundef '(fun (f [y : int]) -> int
                    (if (< y 10)
                        (return 20)
                        (if (< y 2)
                            (return 30)
                            (return (- y 2))))))) (void))

(check-equal? (check-return-paths (parse-fundef '(fun (f [x : int]) -> int
    (begin 
        (declare
            [yes : bool true]
            [i : int 0]
        )
        (set+= i 10)
        (if (< i 20)
            (return i))
        (while (< i 15)
            (set+= i 1))
        (return i))))) (void))

(define top-env 
    (hash
        'fn (FunType '(int bool) 'bool)))

(check-equal? (typecheck-expr (CallExpr 'fn (list (NumExpr 5) 'true)) top-env) 'bool)
(check-exn (regexp (regexp-quote "bad-call")) 
    (lambda () (typecheck-expr (CallExpr 'fn (list 'false 'true)) top-env)))

(check-equal? (typecheck-stmt
    (parse-stmt
        '(begin
            (declare
                [b : bool])
            (set= b (fn 5 false)))) top-env) (void))

(check-equal? (typecheck-stmt
    (parse-stmt
        '(begin
            (fn 5 false))) top-env) (void))

(check-exn (regexp (regexp-quote "bad-assign")) 
    (lambda () (typecheck-stmt
        (parse-stmt
            '(begin
                (declare
                    [b : int])
                (set= b (fn 5 false)))) top-env)))