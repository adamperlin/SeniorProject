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
(check-equal? (parse-expr '(neg 2)) (UnOpExpr 'neg (NumExpr 2)))
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
(check-exn (regexp (regexp-quote "bad-expr: '(@old)")) (lambda () (parse-expr '(@old))))

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

; call statements
(check-equal? (parse-stmt '(f 1 2 3)) (CallStmt 'f (list (NumExpr 1) (NumExpr 2) (NumExpr 3))))

(check-equal? (parse-expr '(f (g 4 5 7) (h true))) (CallExpr 'f (list (CallExpr 'g (list (NumExpr 4) (NumExpr 5) (NumExpr 7)))
                                (CallExpr 'h (list 'true)))))
(check-equal? (parse-expr '(func)) (CallExpr 'func '()))

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
(check-equal? (parse-stmt '((assert (> x 0)) (set= y (- x 1))))
    (AnnoStmt
        (list (Anno 'assert (BinOpExpr '> (IdExpr 'x) (NumExpr 0))))
        (AssignStmt 'set= 'y 
            (BinOpExpr '- 
                (IdExpr 'x)
                (NumExpr 1)))
        ))

(check-equal? (parse-stmt '(
        (assert (> @result 0))
        (assert (< @result z))
        (begin
            (if (> s z)
                (set= s (- z 1)))
            (return s))))
        (AnnoStmt
            (list 
                (Anno 'assert (BinOpExpr '> '@result (NumExpr 0)))
                (Anno 'assert (BinOpExpr '< '@result (IdExpr 'z)))
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
    (Fundef 'f (list (Decl 'x 'int (None)) (Decl 'b 'bool (None))) 'int '() '()
        (RetStmt (Some (IdExpr 'x)))))

(check-equal? (parse-fundef
    '(fun (func) (if true (return 3) (return 4))))
        (Fundef 'func '() 'void '() '()
            (IfStmt 'true
                (RetStmt (Some (NumExpr 3))) (Some (RetStmt (Some (NumExpr 4)))))))
    
(check-exn (regexp (regexp-quote "bad-fundef")) (lambda () (parse-fundef '(fun (fn ())))))
(check-exn (regexp (regexp-quote "bad-stmt")) (lambda () (parse-fundef
    '(fun (f [x : int]) ->))))

(check-equal? (parse-fundef 
    '(fun (f [x : int] [b : bool]) -> int
        (requires (>= x 0))
        (ensures (>= @result 0))
        (return x)))
    (Fundef 'f (list (Decl 'x 'int (None)) (Decl 'b 'bool (None))) 'int
        (list (Contract 'requires (BinOpExpr '>= (IdExpr 'x) (NumExpr 0))))
        (list (Contract 'ensures (BinOpExpr '>= '@result (NumExpr 0))))
        (RetStmt (Some (IdExpr 'x)))))


(check-exn (regexp (regexp-quote "bad-stmt")) 
    (lambda () (parse-fundef 
        '(fun (f [x : int] [b : bool]) -> int
            (requires (>= x 0))
            (ensures (>= @result 0))))))

(check-equal? (parse-fundef 
    '(fun (g [x : int])
        (set= x (* 2 x))))
    (Fundef 'g (list (Decl 'x 'int (None))) 'void '() '()
        (AssignStmt 'set= 'x (BinOpExpr '* (NumExpr 2) (IdExpr 'x)))))

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
                    (set+= i 1)))))))

(check-equal? (parse-fundef big-def) big-def-ast)

; type parsing
(check-equal? (parse-type 'int) 'int)
(check-equal? (parse-type 'bool) 'bool)
(check-equal? (parse-type '(array int)) (ArrayType 'int))
(check-equal? (parse-type '(array (array int))) (ArrayType (ArrayType 'int)))
(check-equal? (parse-type '(array bool)) (ArrayType 'bool))
(check-exn (regexp (regexp-quote "invalid type")) (λ () (parse-type 'bad)))

; forall parsing
(check-equal? (parse-expr
    '(forall ([i : int] [j : int]) #:where (eq? i j) : (eq? (+ i i) (+ i j))))
    (ForallExpr 
        (list (Decl 'i 'int (None)) (Decl 'j 'int (None)))
        (BinOpExpr 'eq? (IdExpr 'i) (IdExpr 'j))
        (BinOpExpr 'eq?
            (BinOpExpr '+ (IdExpr 'i) (IdExpr 'i))
            (BinOpExpr '+ (IdExpr 'i) (IdExpr 'j)))))

; array parsing
(check-equal? (parse-expr '(array-ref arr 0))
                (ArrayRefExpr (IdExpr 'arr) (NumExpr 0)))

(check-equal? (parse-expr '(new-array int 10)) 
    (NewArrayExpr 'int (NumExpr 10)))


(check-exn (regexp (regexp-quote "bad-expr")) 
    (lambda ()
        (parse-expr '(new-array int))))

(check-equal? (parse-expr '(make-array int 10 20 -1 0))
    (MakeArrayExpr 'int (list (NumExpr 10) (NumExpr 20) (NumExpr -1) (NumExpr 0))))

(check-equal? (parse-stmt '(array-set arr 0 (+ 10 4)))
    (ArraySetStmt 'arr (NumExpr 0)
        (BinOpExpr '+ (NumExpr 10) (NumExpr 4))))

(check-equal? (parse-stmt '(array-set arr (- i j) i))
    (ArraySetStmt 'arr (BinOpExpr '- (IdExpr 'i) (IdExpr 'j))
        (IdExpr 'i)))

(define insert-sort '(fun (insert-sort [arr : (array int)])
    (begin
        (declare
            [i : int 0]
            [temp : int])
        (while (< i (length arr))
            (begin
                (declare
                    [j : int (+ i 1)]
                    [min-idx : int i])
                (while (< j (length arr))
                    (begin
                        (if (< (array-ref arr j) (array-ref arr min-idx))
                            (set= min-idx j))
                        (inc j)))
                (set= temp (array-ref arr i)) 
                (array-set arr i (array-ref arr min-idx))
                (array-set arr min-idx temp)
                (inc i))))))

(define fst '(fun (fst [arr : (array int)]) -> int
    (return (array-ref arr 0))))

(check-equal? (parse-expr '(length arr))
    (ArrayLengthExpr (IdExpr 'arr)))


(check-equal? (parse-expr '(length (new-array int 10)))
    (ArrayLengthExpr (NewArrayExpr 'int (NumExpr 10))))

(define fst-ast (Fundef 'fst 
    (list 
        (Decl 'arr (ArrayType 'int) (None))) 'int '() '() 
    (RetStmt (Some (ArrayRefExpr (IdExpr 'arr) (NumExpr 0))))))

(check-equal? (parse-fundef fst) fst-ast)

(define insert-sort-ast (Fundef 'insert-sort 
    (list (Decl 'arr (ArrayType 'int) (None))) 'void '() '() 
    (BeginStmt 
        (list 
            (Decl 'i 'int (Some (NumExpr 0))) 
            (Decl 'temp 'int (None))) 
        (list 
            (WhileStmt 
                (BinOpExpr '< (IdExpr 'i) (ArrayLengthExpr (IdExpr 'arr))) 
                    (BeginStmt 
                        (list 
                            (Decl 'j 'int (Some (BinOpExpr '+ (IdExpr 'i) (NumExpr 1)))) 
                            (Decl 'min-idx 'int (Some (IdExpr 'i)))) 
                        (list 
                            (WhileStmt (BinOpExpr '< (IdExpr 'j) (ArrayLengthExpr (IdExpr 'arr))) 
                                (BeginStmt '() 
                                    (list 
                                        (IfStmt (BinOpExpr '< (ArrayRefExpr (IdExpr 'arr) (IdExpr 'j)) (ArrayRefExpr (IdExpr 'arr) (IdExpr 'min-idx))) 
                                            (AssignStmt 'set= 'min-idx (IdExpr 'j)) (None))
                                        (IncStmt 'j)))) 
                            (AssignStmt 'set= 'temp (ArrayRefExpr (IdExpr 'arr) (IdExpr 'i))) 
                            (ArraySetStmt 'arr (IdExpr 'i) (ArrayRefExpr (IdExpr 'arr) (IdExpr 'min-idx))) 
                            (ArraySetStmt 'arr (IdExpr 'min-idx) (IdExpr 'temp)) 
                            (IncStmt 'i))))))))

(check-equal? (parse-fundef insert-sort) insert-sort-ast)