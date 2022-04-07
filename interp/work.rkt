#lang rosette

; (define-symbolic i j integer?)

; (define (f x y) (+ x y))
; (define h (hash 'ret j))

; (assert (> i (hash-ref h 'ret)))
; (vc-asserts (vc))

(define (max3 args)
    (define x (hash-ref args 'x))
    (define y (hash-ref args 'y))
    (define z (hash-ref args 'z))
    (if (bvsgt x y)
        (if (bvsgt x z)
            (hash-set args 'ret x)
            (hash-set args 'ret z))
        (if (bvsgt y z)
            (hash-set args 'ret y)
            (hash-set args 'ret z))))

(define int32? (bitvector 32))
(define (int32 x) (bv x int32?))
(define-symbolic i j k int32?)
(define args (hash
     'x i
     'y j
     'z k))

; (solve 
;     (let* 
;         ([new-args (max3 args)]
;         [var-i (hash-ref new-args 'x)]
;         [var-j (hash-ref new-args 'y)]
;         [var-k (hash-ref new-args 'z)]
;         [ret (hash-ref new-args 'ret)])
;         (print (hash-ref new-args 'ret))
;         (assert (bvslt ret (int32 0)))))

; (define test-args (hash
;         'x (int32 1)
;         'y (int32 2)
;         'z (int32 3)))
(verify (assert (bveq (hash-ref (max3 args) 'ret) i)))

(define result (max3 args))
(verify (for/all ([v (max3 args) #:exhaustive])
    (assert (bveq (hash-ref (max3 args) 'ret) i))))




#|
    x: 0
    y: 1

    x: 0
    y: 1
    z: 10
|#

'(begin 
    (declare 
        [x : int 0]
        [y : int 1])
    (set= x y)
    (set= y 10)
    (begin 
        (declare 
            [z : int 10])
        (set+= x z))
    (return x))

result

; (hash-ref test-args 'ret)