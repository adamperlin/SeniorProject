#lang rosette

(require "../parser/parser.rkt")
(require "../typecheck/typecheck.rkt")
(require racket/struct)


(provide interp-expr IntValue BoolValue VoidValue Value Frame new-frame interp-stmt interp-prog top-interp)
(struct Value () #:transparent)
(struct IntValue Value [val] #:transparent)
(struct BoolValue Value [val] #:transparent)
(struct VoidValue Value () #:transparent)

(struct/contract Frame ([params hash?] [old-params hash?] [locals-stack list?] [top-env hash?] [return (or/c Value? void?)]) #:transparent #:mutable)
(define/contract (new-frame)
  (-> Frame?)
  (Frame (make-hash) (make-hash) (cons (make-hash) '()) (make-hash) (Value)))

(define/contract (set-local frame name value)
  (-> Frame? symbol? Value? void?)
  (match-let*
      ([(Frame params _ locals-stack _ ret) frame]
       [cur-locals (car locals-stack)])
    
    (cond
      [(hash-has-key? cur-locals name) (let
                                       ([slot (hash-ref cur-locals name)])
                                     (set-box! slot value))]
      [else (hash-set! cur-locals name (box value))])))

(define/contract (get-local frame name)
  (-> Frame? symbol? Value?)
  (match-let*
      ([(Frame params _ locals-stack _ ret) frame]
       [cur-locals (car locals-stack)])
    (unless (hash-has-key? cur-locals name)
      (error 'interp (format "unknown local ~v" name)))
    (unbox (hash-ref cur-locals name))))

(define/contract (modify-local frame name func)
    (-> Frame? symbol? (-> any/c any/c) void?)
    (set-local frame name (func (get-local frame name))))

(define (new-scope frame locals)
  (match-let*
      ([(Frame params _ locals-stack _ ret) frame]
       [next-scope (hash-copy (car locals-stack))])
    (set-Frame-locals-stack! frame (cons next-scope locals-stack))
    (foldl (lambda (decl frame)
        (match-let*
             ([(Decl name typ maybe-expr) decl]
             [val (match maybe-expr 
                    [(Some e) (interp-expr e frame)]
                    [(None) (zero-val-for typ)])])
            (when (hash-has-key? next-scope name)
                (hash-remove! next-scope name))
            (set-local frame name val) frame)) frame locals)) (void))

(define (pop-scope frame)
    (match-let* 
        ([(Frame params _ locals-stack _ ret) frame])
        (set-Frame-locals-stack! frame (cdr locals-stack))))

(define f (new-frame))
(set-local f 'a (IntValue 5))

(define/contract (as-bool b)
  (-> BoolExpr? boolean?)
  (equal? b 'true))

(require (for-syntax syntax/parse racket/base racket/struct))


(begin-for-syntax
    (define (id-prepend str id)
        (datum->syntax id (string->symbol
                            (string-append str
                                            (symbol->string
                                            (syntax->datum id)))))))

(begin-for-syntax
    (define (id-append id str)
        (datum->syntax id (string->symbol
                            (string-append
                                            (symbol->string
                                            (syntax->datum id)) str)))))

(define-syntax (prim stx)
  (syntax-parse stx
    [(_ op t1 t2 ret func)
        (with-syntax ([id (id-prepend "prim" #'op)]
                        [guard1 (id-append #'t1 "?")]
                        [guard2 (id-append #'t2 "?")]
                        [ret-guard (id-append #'ret "?")])
            #'(define/contract (id x y)
                (-> guard1 guard2 ret-guard) 
                (match (cons x y)
                [(cons (t1 v1) (t2 v2)) (ret (func v1 v2))]
                [other (error 'err (format "bad types for ~v: ~v ~v" id x y))])))]
    [(_ op argt ret func)
        (with-syntax ([id (id-prepend "prim" #'op)]
                      [arg-guard (id-append #'argt "?")]
                      [ret-guard (id-append #'ret "?")])

            #'(define/contract (id x) 
                (-> arg-guard ret-guard)
                (match x
                    [(argt v) (ret (func v))]
                    [other (error 'err (format "bad types for ~v: ~v" id x))])))]))

(define/contract (safe-div a b)
  (-> integer? integer? integer?)
  (when (= b 0)
    (error 'divide-by-zero "division by zero"))
    (quotient a b))

(define/contract (shiftl n m)
    (-> integer? integer? integer?)
    (arithmetic-shift n m))

(define/contract (shiftr n m)
    (-> integer? integer? integer?)
    (arithmetic-shift n (- m)))

(prim + IntValue IntValue IntValue +)
(prim - IntValue IntValue IntValue -)
(prim * IntValue IntValue IntValue *)
(prim / IntValue IntValue IntValue safe-div)
(prim % IntValue IntValue IntValue modulo)
(prim band IntValue IntValue IntValue bitwise-and)
(prim bor IntValue IntValue IntValue bitwise-ior)
(prim xor IntValue IntValue IntValue bitwise-xor)
(prim >> IntValue IntValue IntValue shiftr)
(prim << IntValue IntValue IntValue shiftl)
(prim and BoolValue BoolValue BoolValue and)
(prim or BoolValue BoolValue BoolValue or)
(prim > IntValue IntValue BoolValue >)
(prim < IntValue IntValue BoolValue <)
(prim >= IntValue IntValue BoolValue >=)
(prim <= IntValue IntValue BoolValue <=)

; unary operations
(prim ! BoolValue BoolValue not)
(prim ~ IntValue IntValue bitwise-not)
(prim neg IntValue IntValue -)

; inc/dec
(prim add1 IntValue IntValue add1)
(prim sub1 IntValue IntValue sub1)



(define-syntax (fmap-struct stx)
  (syntax-parse stx
    [(_ strct strct-val fn) #'(apply strct (map fn (struct->list strct-val)))]))    

(define/contract (primeq? a b)
  (-> Value? Value? Value?)
  (BoolValue (equal? a b)))

(define/contract (primne? a b)
  (-> Value? Value? Value?)
  (fmap-struct BoolValue (primeq? a b) not))

(define prim-funcs (hash
                       '+ prim+
                       '- prim-
                       '* prim*
                       '/ prim/
                       '% prim%
                       'band primband
                       'bor primbor
                       'xor primxor
                       '>> prim>>
                       '<< prim<<
                       'eq? primeq?
                       'ne? primne?
                       '> prim>
                       '< prim<
                       '>= prim>=
                       '<= prim<=
                       '! prim!
                       '~ prim~
                       'neg primneg
                       'and primand
                       'or primor))


;(define binop-bool-funcs)



(define/contract (interp-binop op lft-val rht-val)
  (-> BinOp? Value? Value? Value?)
  (unless (hash-has-key? prim-funcs op)
    (error 'interp (format "invalid binop ~v" op)))
  ((hash-ref prim-funcs op) lft-val rht-val))

(define/contract (interp-unop op val)
    (-> UnOp? Value? Value?)
    (unless (hash-has-key? prim-funcs op)
        (error 'interp (format "invalid unop ~v" op)))
        ((hash-ref prim-funcs op) val))


(define (zip-decls args decls)
    (map 
        (lambda (expr decl) (Decl (Decl-name decl) (Decl-typ decl) (Some expr)))
                            args decls))

(define (store-old frame fargs)
    (match-let* 
        ([(Frame _ old-params _ _ _) frame])
        (for/list ([decl fargs])
            (let 
                ([name (Decl-name decl)])
                (hash-set! old-params name (box (get-local frame name)))))))

(define (eval-contract con frame)
    (match-let*
        ([(Contract ctype expr) con]
         [pass (interp-expr expr frame)])
        (unless (BoolValue-val pass)
            (error ctype (format "contract check failed; frame state ~v" (car (Frame-locals-stack frame)))))))

(define (interp-call id arg-exprs frame)
    (match-let*
        ([(Frame params _ locals top-env return) frame]
         [(Fundef id fargs rtype reqs ens body) (hash-ref top-env id)]
         [new-frame (Frame (make-hash) (make-hash) (list (make-hash)) (Frame-top-env frame) (VoidValue))]
         [arg-decls (zip-decls arg-exprs fargs)])
        (begin 
            (new-scope frame arg-decls)
            (store-old frame fargs)
            (for/list ([req reqs])
                (eval-contract req frame))
            (interp-stmt body frame)
            (for/list ([en ens])
                (eval-contract en frame))
            (Frame-return frame))))

(define/contract (interp-call-expr expr frame)
    (-> CallExpr? Frame? Value?)
    (match-let*
        ([(CallExpr id cargs) expr])
        (interp-call id cargs frame)))

(define/contract (interp-call-stmt stmt frame)
    (-> CallStmt? Frame? symbol?)
    (match-let*
        ([(CallStmt id cargs) stmt])
        (interp-call id cargs frame)
        'continue))

(define (interp-old-expr old-expr frame)
    (match-let*
        ([(OldExpr expr) old-expr]
         [(Frame _ old-params locals-stack _ _) frame])
        (begin
            (set-Frame-locals-stack! frame (cons old-params locals-stack))
            (define res (interp-expr expr frame))
            (set-Frame-locals-stack! frame (cdr (Frame-locals-stack frame)))
            res)))

(define/contract (interp-expr expr frame)
  (-> Expr? Frame? Value?)
  (match expr
    [(NumExpr n) (IntValue n)]
    [(? BoolExpr? b) (BoolValue (as-bool b))]
    [(IdExpr id) (get-local frame id)]
    [(BinOpExpr op lft rht) (interp-binop op
                                          (interp-expr lft frame)
                                          (interp-expr rht frame))]
    [(CallExpr id args) (interp-call-expr expr frame)]
    [(UnOpExpr op expr) (interp-unop op (interp-expr expr frame))]
    [(OldExpr _) (interp-old-expr expr frame)]
    ['@result (Frame-return frame)]))


(define/contract (interp-inc inc frame)
    (-> IncStmt? Frame? void?)
    (match-let*
        ([(IncStmt lv) inc])
        (modify-local frame lv primadd1)))

(define/contract (interp-dec dec-expr frame)
    (-> DecStmt? Frame? void?)
    (match-let*
        ([(DecStmt lv) dec-expr])
        (modify-local frame lv primsub1)))

(define assign-funcs (hash
                    'set+= prim+ 
                    'set-= prim- 
                    'set/= prim/
                    'set*= prim*
                    'set>>= prim>>
                    'set<<= prim<< 
                    'set^= primxor 
                    'set&= primband
                    'set-bor= primbor
                    'set= const))

(define/contract (interp-assign assign-stmt frame)
    (-> AssignStmt? Frame? void?)
    (match-let* 
        ([(AssignStmt op target src) assign-stmt]
         [src-val (interp-expr src frame)])
         (modify-local frame target (curryr (hash-ref assign-funcs op) src-val))))

(define/contract (interp-if if-stmt frame)
    (-> IfStmt? Frame? symbol?)
    (match-let* 
        ([(IfStmt guard then els) if-stmt]
         [guard-val (interp-expr guard frame)])
         (match guard-val
            [(BoolValue #t) (interp-stmt then frame)]
            [(BoolValue #f) 
                (match els
                    [(Some els-stmt) (interp-stmt (Some-v els) frame)]
                    [None 'continue])])))


(define/contract (interp-ret ret-stmt frame)
    (-> RetStmt? Frame? symbol?)
    (match ret-stmt
        [(RetStmt (Some e)) (let ([val (interp-expr e frame)])
                                (begin
                                    (set-Frame-return! frame val)
                                    'return))]
        [(RetStmt (None)) (begin 
            (set-Frame-return! frame (void))
            'return)]))

(define/contract (interp-while while-stmt frame)
    (-> WhileStmt? Frame? symbol?)
    (match-let*
        ([(WhileStmt guard body) while-stmt]
        [(BoolValue b) (interp-expr guard frame)])
        (if b 
            (let 
                ([body-signal (interp-stmt body frame)])
                (match body-signal
                    ['return 'return]
                    ['continue (interp-while while-stmt frame)])) 'continue)))
    
(define (zero-val-for typ)
    (match typ
        ['int (IntValue 0)]
        ['bool (BoolValue #f)]))


(define (interp-sequence stmts frame) 
    (match stmts
        ['() 'continue]
        [(cons fst rst) (let 
                            ([fst-val (interp-stmt fst frame)])
                            (if (equal? fst-val 'return)
                                'return
                                (interp-sequence rst frame)))]))

(define/contract (interp-begin begin-stmt frame)
    (-> BeginStmt? Frame? symbol?)
    (match-let*
        ([(BeginStmt decls stmts) begin-stmt])
         (begin 
            (new-scope frame decls)
            (define ret-signal (interp-sequence stmts frame))
            (pop-scope frame)
            ret-signal)))

(define/contract (interp-fundef fundef tenv)
    (-> Fundef? hash? void?)
    (hash-set! tenv (Fundef-id fundef) fundef))

(define action-continue 'continue)
(define action-return 'return)
(define/contract (interp-stmt stmt frame)
    (-> Stmt? Frame? symbol?)
    (match stmt
        [(RetStmt _) (interp-ret stmt frame)]
        [(IncStmt lv) (interp-inc stmt frame) 'continue]
        [(DecStmt lv) (interp-dec stmt frame) 'continue]
        [(AssignStmt op target src) (interp-assign stmt frame) 'continue]
        [(IfStmt _ _ _ ) (interp-if stmt frame)]
        [(WhileStmt _ _) (interp-while stmt frame)]
        [(BeginStmt _ _) (interp-begin stmt frame)]
        [(CallStmt _ _) (interp-call-stmt stmt frame)]
        [(AnnoStmt _ _) (interp-anno-stmt  stmt frame)]))

(define (eval-ann ann frame)
    (match-let*
        ([(Anno vtype expr) ann]
         [pass (interp-expr expr frame)])
        (unless (BoolValue-val pass)
            (error vtype (format "validation failed; frame state ~v" (car (Frame-locals-stack frame)))))))

(define (interp-anno-stmt anno-stmt frame)
    (match-let*
        ([(AnnoStmt anns stmt) anno-stmt])
        (map (curryr eval-ann frame) anns)
        (interp-stmt stmt frame)))

(define/contract (interp-prog fundefs)
    (-> list? Value?)
    (let
        ([tenv (make-hash)])
        (map (curryr interp-fundef tenv) fundefs)
        (begin
            (unless (hash-has-key? tenv 'main)
                (error 'no-main "no main function defined"))
            (define initial-frame (Frame (make-hash) (make-hash) (list (make-hash)) tenv (VoidValue)))
            (define main-call (CallStmt 'main '()))
            (interp-stmt main-call initial-frame)
            (Frame-return initial-frame))))

(define (top-interp prog)
    (begin 
        (define fundefs (map parse-fundef prog))
        (typecheck-program fundefs)
        (interp-prog fundefs)))