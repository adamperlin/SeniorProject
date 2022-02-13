#lang typed/racket

(require "parser.rkt")
(require typed/rackunit)

; numeric expressions
(check-equal? (parse-expr 3) (NumExpr 3))
(check-equal? (parse-expr 132432) (NumExpr 132432))
(check-equal? (parse-expr -234) (NumExpr -234))

; id expressions
(check-equal? (parse-expr 'x) (IdExpr 'x))

;(check-equal? (parse-expr 'if) (IdExpr 'y))

; boolean (true|false) constant expressions
(check-equal? (parse-expr 'true) 'true)
(check-equal? (parse-expr 'false) 'false)

; binary expressions
(check-equal? (parse-expr '(+ x 3))
              (BinOpExpr
               '+
               (IdExpr 'x)
               (NumExpr 3)))
(check-equal? (parse-expr '(* (+ x 1) (/ x 2)))
                          (BinOpExpr '*
                                     (BinOpExpr '+
                                                (IdExpr 'x)
                                                (NumExpr 1))
                                     (BinOpExpr '/
                                                (IdExpr 'x)
                                                (NumExpr 2))))

(check-exn (regexp (regexp-quote "bad-expr")) (lambda () (parse-expr '(+ 2))))

; unary expressions
(check-equal? (parse-expr '(- 2)) (UnOpExpr '- (NumExpr 2)))
(check-equal? (parse-expr '(! true)) (UnOpExpr '! 'true))
(check-exn (regexp (regexp-quote "bad-expr")) (lambda () (parse-expr '(! while))))

; result expr
(check-equal? (parse-expr '@result) '@result)

; old(e..) expr
(check-equal? (parse-expr '(old (>= x 0)))
                          (OldExpr
                           (BinOpExpr '>=
                                      (IdExpr 'x)
                                      (NumExpr 0))))
(check-exn (regexp (regexp-quote "bad-expr: '(old)")) (lambda () (parse-expr '(old))))

; simple statements
(check-equal? (parse-stmt '(inc x)) (IncStmt 'x))
(check-equal? (parse-stmt '(dec x)) (DecStmt 'x))
(check-exn (regexp (regexp-quote "bad-stmt")) (lambda () (parse-stmt '(inc))))
(check-exn (regexp (regexp-quote "bad-stmt")) (lambda () (parse-stmt '(dec))))
(check-equal? (parse-stmt '(return (+ 2 (* 3 x)))) (RetStmt (Some (BinOpExpr '+ (NumExpr 2) (BinOpExpr '* (NumExpr 3) (IdExpr 'x))))))
(check-equal? (parse-stmt '(return)) (RetStmt (None)))
(check-equal? (parse-stmt '(set+= v 3)) (AssignStmt 'set+= 'v (NumExpr 3)))
(check-equal? (parse-stmt '(set>>= v 2)) (AssignStmt 'set>>= 'v (NumExpr 2)))
(check-exn (regexp (regexp-quote "bad-stmt")) (lambda () (parse-stmt '(set*= v))))

; if statements
(check-equal? (parse-stmt '(if (< x 10) (set+= x 2) (set-= x 3))) (IfStmt
                                                                   (BinOpExpr
                                                                    '<
                                                                    (IdExpr 'x)
                                                                    (NumExpr 10))
                                                                   (AssignStmt 'set+= 'x (NumExpr 2))
                                                                   (Some (AssignStmt 'set-= 'x (NumExpr 3)))))
(check-equal? (parse-stmt '(if (eq? x y) (return 7))) (IfStmt
                                                       (BinOpExpr
                                                        'eq?
                                                        (IdExpr 'x)
                                                        (IdExpr 'y))
                                                       (RetStmt (Some (NumExpr 7)))
                                                       (None)))

(check-exn (regexp (regexp-quote "bad-stmt")) (λ () (parse-stmt '(if (< x y)))))
(check-exn (regexp (regexp-quote "bad-stmt")) (λ () (parse-stmt 'if)))

; while statements
(check-equal? (parse-stmt '(while (ne? y z) (inc y))) (WhileStmt (BinOpExpr 'ne? (IdExpr 'y) (IdExpr 'z))
                                                            (IncStmt 'y)))
(check-equal? (parse-stmt '(while true (set+= x 8))) 
    (WhileStmt 'true (AssignStmt 'set+= 'x (NumExpr 8))))

(check-exn (regexp (regexp-quote "bad-stmt")) (λ () (parse-stmt '(while (>= x y)))))

; begin statements
(check-equal? (parse-stmt '(begin (set+= x 1) (set*= y 2))) 
    (BeginStmt '() (list (AssignStmt 'set+= 'x (NumExpr 1)) (AssignStmt 'set*= 'y (NumExpr 2)))))

(check-equal? (parse-stmt '(begin (declare
    [x : int 9]
    [yes : bool false]) (set= isYes yes)))
        (BeginStmt (list (Decl 'x 'int (Some (NumExpr 9))) (Decl 'yes 'bool (Some 'false)))
            (list (AssignStmt 'set= 'isYes (IdExpr 'yes)))))

(check-equal? (parse-stmt '(begin (declare [truthy : bool]))) (BeginStmt (list (Decl 'truthy 'bool (None))) '()))

; annotated statements
(check-equal? (parse-stmt '((requires (> x 0)) (set= y (- x 1))))
    (AnnoStmt
        (list (Anno 'requires (BinOpExpr '> (IdExpr 'x) (NumExpr 0))))
        (AssignStmt 'set= 'y 
            (BinOpExpr '- 
                (IdExpr 'x)
                (NumExpr 1)))
        ))

(check-equal? (parse-stmt '(
        (ensures (> @result 0))
        (ensures (< @result z))
        (begin
            (if (> s z)
                (set= s (- z 1)))
            (return s))))
        (AnnoStmt
            (list 
                (Anno 'ensures (BinOpExpr '> '@result (NumExpr 0)))
                (Anno 'ensures (BinOpExpr '< '@result (IdExpr 'z)))
            )
            (BeginStmt '()
                (list 
                   (IfStmt (BinOpExpr '> (IdExpr 's) (IdExpr 'z))
                        (AssignStmt 'set= 's (BinOpExpr '- (IdExpr 'z) (NumExpr 1))) (None)) 
                   (RetStmt (Some (IdExpr 's)))))))

(check-exn (regexp (regexp-quote "bad-stmt")) (lambda () (parse-stmt '(ensures (> x y)))))
(check-exn (regexp (regexp-quote "bad-stmt")) (lambda () (parse-stmt '(
    (ensures (> x y))
    (invariant (< x 2))))))

(check-equal? (parse-fundef 
    '(fun (f [x : int] [b : bool]) -> int
        (return x)))
    (Fundef 'f (make-hash (list (cons 'x 'int) (cons 'b 'bool))) 'int
        (RetStmt (Some (IdExpr 'x)))))

(check-equal? (parse-fundef
    '(fun (func) (if true (return 3) (return 4))))
        (Fundef 'func (make-hash) 'void
            (IfStmt 'true
                (RetStmt (Some (NumExpr 3))) (Some (RetStmt (Some (NumExpr 4)))))))
    
(check-exn (regexp (regexp-quote "bad-fundef")) (lambda () (parse-fundef '(fun (fn ())))))
(check-exn (regexp (regexp-quote "bad-stmt")) (lambda () (parse-fundef
    '(fun (f [x : int]) ->))))

(define big-def-ast (Fundef 'sum (make-hash '((n . int))) 'int
    (AnnoStmt
        (list
            (Anno 'requires (BinOpExpr '>= (IdExpr 'n) (NumExpr 0)))
            (Anno 'ensures (BinOpExpr 'eq?
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
                                    (AssignStmt 'set+= 'i (NumExpr 1)))))))))))
(define big-def '(fun (sum [n : int]) -> int
    ((requires (>= n 0))
     (ensures (eq? @result (/ (* n (+ n 1)) 2)))
        (begin
            (declare 
                [i : int 1]
                [sum : int 0])
            (while (<= i n)
                ((invariant (eq? sum (/ (* i (- i 1)) 2)))
                    (begin
                        (set+= sum i)
                        (set+= i 1))))))))

(check-equal? (parse-fundef big-def) big-def-ast)