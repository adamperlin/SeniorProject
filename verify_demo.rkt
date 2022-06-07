#lang rosette

(require "./interp/interp.rkt")
(require "./parser/parser.rkt")
(require "./typecheck/typecheck.rkt")

(define examples (hash
    ; this should pass - simply swapping multiplication for addition
    'double (parse-fundef 
                '(fun (double [x : int]) -> int
                    (ensures (eq? @result (* 2 x)))
                    (return (+ x x))))

    ; this is obvoiusly incorrect
    'bad-double (parse-fundef 
                '(fun (double [x : int]) -> int
                    (ensures (eq? @result (* 2 x)))
                    (return (+ (+ x x) 1))))

    ; there should be no issues with logic here
    'basic-max (parse-fundef '(fun (max [x : int] [y : int]) -> int
        (ensures (or (eq? @result x) (eq? @result y)))
        (ensures (and (>= @result y) 
                      (>= @result x)))
        (if (> x y)
            (return x)
            (return y))))
    
    ; specification is wrong here and will fail if result is y
    'bad-max (parse-fundef 
        '(fun (max [x : int] [y : int]) -> int
            (ensures (eq? @result x)) ; needs to account for (eq? @result y)
            (if (> x y)
                (return x)
                (return y))))

    ; slightly more complicated logic here but this should work 
    'max3 (parse-fundef 
    '(fun (max3 [x : int] [y : int] [z : int]) -> int
        (ensures (or (eq? @result x) (or (eq? @result y) (eq? @result z))))
        (ensures (and (>= @result x) (and (>= @result y) (>= @result z))))
        (begin
            (if (> x y)
                (if (> x z)
                    (return x))
                (if (> y z)
                    (return y)))
            (return z))))
    
    ; simple looping case
      'count-up (parse-fundef '(fun (count-up [n : int]) -> int
        (requires (and (>= n 1) (< n 100)))
        (requires (>= n 1))
        (ensures (eq? @result n))
            (begin
                (declare 
                    [i : int 1])
                (while (< i n)
                        (begin
                            (set+= i 1)))
                (return i))))
        
        ; canonical 'sum' looping example
        'sum (parse-fundef '(fun (sum [n : int]) -> int
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
                    (return sum))))
            
        ; sum but with an off-by-one error (contract should be verifiably correct)
        'bad-sum (parse-fundef '(fun (sum [n : int]) -> int
                    (requires (and (>= n 0) (< n 100)))
                    (ensures (eq? @result (/ (* n (+ n 1)) 2)))
                    (begin
                        (declare 
                            [i : int 1]
                            [sum : int 0])
                        ; off by one error
                        (while (< i n)
                            (begin
                                (set+= sum i)
                                (set+= i 1)))
                        (return sum))))
        
        ; integer log - contract should be verifiably correct (within 100 iters)
        'log (parse-fundef '(fun (log [x : int]) -> int
                                (requires (and (>= x 1) (< x 100)))
                                (ensures (>= @result 0))
                                (ensures (<= (<< 1 @result) x))
                                (begin
                                    (declare 
                                        [r : int 0]
                                        [y : int x])
                                    (while (> y 1)
                                            (begin
                                                (inc r)
                                                (set= y (/ y 2))))
                                    (return r))))
        
        ; log with an off-by-one; needs to stop when y is 1
        'bad-log (parse-fundef '(fun (log [x : int]) -> int
                                (requires (and (>= x 1) (< x 100)))
                                (ensures (>= @result 0))
                                (ensures (<= (<< 1 @result) x))
                                (begin
                                    (declare 
                                        [r : int 0]
                                        [y : int x])
                                    ; another off-by-one
                                    (while (>= y 1)
                                            (begin
                                                (inc r)
                                                (set= y (/ y 2))))
                                    (return r))))
        'sum-even (parse-fundef '(fun (sum-even [n : int]) -> int
                                    (requires (and (>= n 1) (< n 50))) 
                                    (ensures (>= @result 0))
                                    (ensures (eq? @result (* n (+ n 1))))
                                (begin
                                    (declare
                                        [sum : int 0]
                                        [i : int 1])
                                    (while (<= i (* 2 n))
                                        (begin 
                                            (if (eq? (% i 2) 0)
                                                (set+= sum i))
                                            (inc i)))
                                    (return sum))))))
        

(define (display-result res)
    (cond
        [(union? res) (find-single-counter-ex res)]
        [(and (list? res) (not (empty? res))) (find-single-counter-ex res)]
        [else res]))

; the a nested union of many different models which
; violate the verification conditions will often be returned from verify-fun
; since verification is split into several conditional paths 
; it is nice to walk this structure and return just a single counter-example
(define (find-single-counter-ex u)
    (cond
        [(sat? u) u]
        [(list? u) (let ([f (filter sat? (map find-single-counter-ex u))])
                         (car f))]
        [(union? u) (let ([f (filter sat? (map find-single-counter-ex (map cdr (union-contents u))))])
                         (car f))]
        [else u]))

(for ([(name fun) examples])
    (printf "verifying ~v...\n" name)
    (typecheck-function fun (hash))
    (let ([ver-res (verify-fun fun)])
        (printf "verification result: ~v\n" (display-result ver-res))))