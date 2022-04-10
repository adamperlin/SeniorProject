#lang rosette

(require "../parser/parser.rkt")
(require "../typecheck/typecheck.rkt")
(require racket/struct)


(provide int32 int32? verify-fun interp-expr 
    Scope new-scope push-scope set-local get-local Binding IntValue BoolValue VoidValue Value Frame new-frame interp-stmt interp-prog top-interp)

; values which can be produced through iterpretation
(struct Value () #:transparent)
(struct IntValue Value [val] #:transparent)
(struct BoolValue Value [val] #:transparent)
(struct VoidValue Value () #:transparent)

(define int32? (bitvector 32))
(define (int32 x) (bv x int32?))

; represents an instance of a stack frame for a single function
; note that because nested scopes can be defined dynamically, the
; frame has its own internal stack, locals-stack, for pushing and popping the internal scopes
(struct/contract Frame ([params hash?] [old-params hash?] [locals-stack list?] [top-env hash?] [return (or/c Value? void?)]) #:transparent)
(define/contract (new-frame)
  (-> Frame?)
  (Frame (hash) (hash) (list (Scope 0 (hash))) (hash) (Value)))


(struct Scope [id bindings] #:transparent)
(struct Binding [id value] #:transparent)

; sets the value of a local variable in the current scope
(define (set-local frame name value)
  (match-let*
      ([(Frame params _ locals-stack _ ret) frame]
       [scope (car locals-stack)]
       [new-locals (struct-copy Scope scope
                            [bindings 
                                (hash-set (Scope-bindings scope) 
                                    name 
                                    (Binding (Scope-id scope) value))])])
    (struct-copy Frame frame 
        [locals-stack 
            (cons new-locals
                (cdr locals-stack))])))

(define (get-local frame name)
  (match-let*
      ([(Frame params _ locals-stack _ ret) frame]
       [(Scope id bindings) (car locals-stack)])
    (unless (hash-has-key? bindings name)
      (error 'interp (format "unknown local ~v" name)))
    (Binding-value (hash-ref bindings name))))

; unbox, apply function to internal value, and re-box local binding
(define/contract (modify-local frame name func)
    (-> Frame? symbol? (-> any/c any/c) Frame?)
    (set-local frame name (func (get-local frame name))))

; creates a new scope by pushing a new hashmap onto the local scopes stack
(define (new-scope frame locals)
  (match-let*
      ([(Frame params _ locals-stack _ ret) frame]
       [cur-scope (car locals-stack)]
        ; we copy the bindings that are in the top entry of the local stack into our nested scope,
       [next-scope (struct-copy
                        Scope
                        cur-scope
                        [id (+ 1 (Scope-id cur-scope))])]
        [new-frame (push-scope frame next-scope)])
    (foldl (lambda (decl frame)
        (match-let*
             ([(Decl name typ maybe-expr) decl]
             ; evaluate the associated expression in each new binding
             [val (match maybe-expr 
                    [(Some e) (interp-expr e frame)]
                    [(None) (zero-val-for typ)])])
            (set-local frame name val))) new-frame locals)))

(define (pop-scope frame)
    (match-let* 
        ([(Frame params _ locals-stack _ ret) frame])
        (struct-copy Frame frame [locals-stack (cdr locals-stack)])))

(define (push-scope frame scope)
    (match-let*
        ([(Frame params _ locals-stack _ ret) frame])
        (struct-copy Frame frame [locals-stack (cons scope locals-stack)])))

(define/contract (as-bool b)
  (-> BoolExpr? boolean?)
  (equal? b 'true))

(require (for-syntax syntax/parse racket/base racket/struct))

; prepends the string str onto a racket identifier
; based heavily on
; https://www.it.uu.se/edu/course/homepage/avfunpro/ht13/lectures/Racket-3-Macros.pdf, 
; "Breaking Hygiene"
(begin-for-syntax
    (define (id-prepend str id)
        (datum->syntax id (string->symbol
                            (string-append str
                                            (symbol->string
                                            (syntax->datum id)))))))

; appends the string str onto the end of a racket identifier
(begin-for-syntax
    (define (id-append id str)
        (datum->syntax id (string->symbol
                            (string-append
                                            (symbol->string
                                            (syntax->datum id)) str)))))

#|
   The following are macros for generating primitive operators
   For instance, (prim + IntValue IntValue IntValue +) defines the function 'prim+' 
   that has a contract which accepts only IntValues and returns an IntValue.
   It will unwrap the intv alues, and invoke the function '+' (last argument)
   on the unwrapped internal value
|#
(define-syntax (prim stx)
  (syntax-parse stx
    [(_ op t1 t2 ret func)
        (with-syntax ([id (id-prepend "prim" #'op)])
            #'(define (id x y)
                (match (cons x y)
                [(cons (t1 v1) (t2 v2)) (ret (func v1 v2))]
                [other (error 'err (format "bad types for ~v: ~v ~v" id x y))])))]
    ; unary operation variant
    [(_ op argt ret func)
        (with-syntax ([id (id-prepend "prim" #'op)])
            #'(define (id x) 
                (match x
                    [(argt v) (ret (func v))]
                    [other (error 'err (format "bad types for ~v: ~v" id x))])))]))

(define/contract (safe-div a b)
  (-> int32? int32? int32?)
  (when (bveq b (int32 0))
    (error 'divide-by-zero "division by zero"))
    (bvsdiv a b))

(define/contract (shiftl n m)
    (-> int32? int32? int32?)
    (bvshl n m))

(define/contract (shiftr n m)
    (-> int32? int32? int32?)
    (bvashr n m))

(define bvadd1 (curryr bvadd (int32 1)))
(define bvsub1 (curryr bvsub (int32 1)))

; primitive definitions using the macros...
(prim + IntValue IntValue IntValue bvadd)
(prim - IntValue IntValue IntValue bvsub)
(prim * IntValue IntValue IntValue bvmul)
(prim / IntValue IntValue IntValue safe-div)
(prim % IntValue IntValue IntValue bvsmod)
(prim band IntValue IntValue IntValue bvand)
(prim bor IntValue IntValue IntValue bvor)
(prim xor IntValue IntValue IntValue bvxor)
(prim >> IntValue IntValue IntValue shiftr)
(prim << IntValue IntValue IntValue shiftl)
(prim and BoolValue BoolValue BoolValue &&)
(prim or BoolValue BoolValue BoolValue ||)
(prim > IntValue IntValue BoolValue bvsgt)
(prim < IntValue IntValue BoolValue bvslt)
(prim >= IntValue IntValue BoolValue bvsge)
(prim <= IntValue IntValue BoolValue bvsle)

; unary operations
(prim ! BoolValue BoolValue not)
(prim ~ IntValue IntValue bvnot)
(prim neg IntValue IntValue bvneg)

; inc/dec
(prim add1 IntValue IntValue bvadd1)
(prim sub1 IntValue IntValue bvsub1)

; there is probably a more rackety way to do this, but 
; essentially this is a macro which generates a map of a function
; over each of a struct's fields, before wrapping the fields back
; in the struct. It is a lot like a simple fmap on a product type in haskell
(define-syntax (fmap-struct stx)
  (syntax-parse stx
    [(_ strct strct-val fn) #'(apply strct (map fn (struct->list strct-val)))]))    

(define/contract (primeq? a b)
  (-> Value? Value? Value?)
  (match (cons a b)
    [(cons (IntValue i) (IntValue j)) (BoolValue (bveq i j))]
    [(cons (BoolValue k) (BoolValue l)) (BoolValue (equal? k l))]))

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


; zip list of args (expressions) and list of declarations 
; into declarations annotated with the expressions
; declarations have an optional expression, hence the 'Some'
(define (zip-decls args decls)
    (map 
        (lambda (expr decl) (Decl (Decl-name decl) (Decl-typ decl) (Some expr)))
                            args decls))

; we store copies of function arguments
; on entry to the function in order to 
; support the (old e) syntax, where e is an expression evaluated with respect to
; the parameters of the function when it was entered.
(define (store-old frame fargs)
    (match-let* 
        ([(Frame _ old-params _ _ _) frame]
         [old (foldl (lambda (decl old-map)
            (let*
                ([name (Decl-name decl)]
                [val (get-local frame name)])
            (hash-set old-map name val)) (hash) fargs))])
            (struct-copy Frame frame [old-params old])))

(define (eval-contract con frame)
    (match-let*
        ([(Contract ctype expr) con]
         [pass (interp-expr expr frame)])
        (unless (BoolValue-val pass)
            (error ctype (format "contract check failed; frame state ~v" (car (Frame-locals-stack frame)))))))

(define (bind-frame-comp comp f)
    (lambda (frame) 
        (match-let*
            ([(cons res new-frame) (comp frame)]
            [frame-act (f res)])
        (frame-act new-frame))))

(define (lift-frame-comp a)
    (lambda (frame)
        (cons (a frame))))

(define (interp-call id arg-exprs frame)
    (match-let*
        ([(Frame params _ locals top-env return) frame]
         [(Fundef id fargs rtype reqs ens body) (hash-ref top-env id)]
         [new-frame (Frame (make-hash) (make-hash) (list (make-hash)) (Frame-top-env frame) (VoidValue))]
         [arg-decls (zip-decls arg-exprs fargs)])
        (begin 
            (new-scope frame arg-decls)
            (store-old frame fargs)
            ; evaluate 'requires' preconditions
            (for/list ([req reqs])
                (eval-contract req frame))
            (interp-stmt body frame)
            ; evalaute 'ensures' post conditions
            (for/list ([en ens])
                (eval-contract en frame))
            ; return value for a function is stored in the 'return' slot of the frame
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

; (define (interp-old-expr old-expr frame)
;     (match-let*
;         ([(OldExpr expr) old-expr]
;          [(Frame _ old-params locals-stack _ _) frame])
;         (begin
;             (set-Frame-locals-stack! frame (cons old-params locals-stack))
;             (define res (interp-expr expr frame))
;             (set-Frame-locals-stack! frame (cdr (Frame-locals-stack frame)))
;             res)))

(define/contract (interp-expr expr frame)
  (-> Expr? Frame? Value?)
  (match expr
    [(NumExpr n) (IntValue (int32 n))]
    [(? BoolExpr? b) (BoolValue (as-bool b))]
    [(IdExpr id) (get-local frame id)]
    [(BinOpExpr op lft rht) (interp-binop op
                                          (interp-expr lft frame)
                                          (interp-expr rht frame))]
    [(CallExpr id args) (interp-call-expr expr frame)]
    [(UnOpExpr op expr) (interp-unop op (interp-expr expr frame))]
    ;[(OldExpr _) (interp-old-expr expr frame)]
    ['@result (Frame-return frame)]))


(define/contract (interp-inc inc frame)
    (-> IncStmt? Frame? pair?)
    (match-let*
        ([(IncStmt lv) inc])
        (cons 'continue (modify-local frame lv primadd1))))

(define/contract (interp-dec dec-expr frame)
    (-> DecStmt? Frame? pair?)
    (match-let*
        ([(DecStmt lv) dec-expr])
        (cons 'continue (modify-local frame lv primsub1))))

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
    (-> AssignStmt? Frame? pair?)
    (match-let* 
        ([(AssignStmt op target src) assign-stmt]
         [src-val (interp-expr src frame)])
         ; we can implement our assignments by using the macro generated primitives,
         ; and the simply using modify-local to read the value of a binding, apply a function,
         ; and then store it again
         (cons
            'continue
            (modify-local frame target (curryr (hash-ref assign-funcs op) src-val)))))

(define/contract (interp-if if-stmt frame)
    (-> IfStmt? Frame? pair?)
    (match-let* 
        ([(IfStmt guard then els) if-stmt]
         [guard-val (interp-expr guard frame)])
         (if (BoolValue-val guard-val)
            (interp-stmt then frame)
            (match els
                    [(Some els-stmt) (interp-stmt (Some-v els) frame)]
                    [None (cons 'continue frame)]))))

; returns involve simply setting the return slot in the interpreter stack frame, 
; and returning a 'return symbol, which indicates to the caller to propagate 
; the return signal upwards
(define/contract (interp-ret ret-stmt frame)
    (-> RetStmt? Frame? pair?)
    (match ret-stmt
        [(RetStmt (Some e)) (let ([val (interp-expr e frame)])
                                    (cons 'return (struct-copy Frame frame [return val])))]
        [(RetStmt (None)) 
            (cons 'return (struct-copy Frame frame [return (VoidValue)]))]))

; while's are fairly self-explanatory, but they need
; to handle a possible 'return signal from the child statement
; note that 'continue here means continue, don't return. It doesn't correspond to 
; any kind of "continue" statement
(define/contract (interp-while while-stmt frame)
    (-> WhileStmt? Frame? pair?)
    (match-let*
        ([(WhileStmt guard body) while-stmt]
        [(BoolValue b) (interp-expr guard frame)])
        (if b 
            (match-let* 
                ([(cons body-signal new-frame) (interp-stmt body frame)])
                (match body-signal
                    ['return (cons 'return new-frame)]
                    ['continue (interp-while while-stmt new-frame)])) 
            (cons 'continue frame))))
    
(define (zero-val-for typ)
    (match typ
        ['int (IntValue (int32 0))]
        ['bool (BoolValue #f)]))

; we deal with early returns as a base case when we're interpreting a sequence of statements...
; at each step we either recurse and continue, or propagate the 'return upwards
(define (interp-sequence stmts frame) 
    (match stmts
        ['() 'continue]
        [(cons fst rst) (let 
                            ([fst-val (interp-stmt fst frame)])
                            (if (equal? fst-val 'return)
                                'return
                                (interp-sequence rst frame)))]))

; begin statements involve the introduction of a new scope, so we may be adding
; to the locals stack here in addition to interpreting a sequence of statements
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
    (-> Stmt? Frame? pair?)
    (match stmt
        [(RetStmt _) (interp-ret stmt frame)]
        [(IncStmt lv) (interp-inc stmt frame)]
        [(DecStmt lv) (interp-dec stmt frame)]
        [(AssignStmt op target src) (interp-assign stmt frame)]
        ; these statements could propagate a 'return upwards, so we let them decide
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

; interpreting an annotated statement simply involves checking the assertions 
; for truthiness and crashing if they fail, before executing the associated statement
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

(define (eval-contract-cond con frame)
    (match-let*
        ([(Contract ctype expr) con]
         [res (interp-expr expr frame)])
         (BoolValue-val res)))


(define (rosette-type ty)
    (match ty
        ['int int32?]
        ['bool boolean?]))

(define (value-type ty)
    (match ty
        ['int IntValue]
        ['bool BoolValue]))

(define (fresh-var decl)
    (match-let*
        ([(Decl name ty _) decl])
        ((value-type ty) (constant name (rosette-type ty)))))

(define (verify-fun fundef)
    (match-let*
        ([(Fundef id fargs rtype requires ensures body) fundef]
         [frame (Frame (make-hash) (make-hash) (list (make-hash)) (make-hash) (VoidValue))])
         (define cur-scope (make-hash))
         (begin
            (print "here")
            (print fargs)
            (foldl (lambda (decl args)
                (begin 
                    (hash-set! args (Decl-name decl) (box (fresh-var decl)))
                 args))
                cur-scope
                fargs)
            ;(set-Frame-params! frame (hash-copy cur-scope))
            (println (format "cur-scope: ~v" cur-scope))
            (push-scope frame cur-scope)
            ;(store-old frame fargs)
            ; evaluate 'requires' preconditions
            ;(for/list ([req reqs])
            ;    (eval-contract req frame))
            (interp-stmt body frame)
            (println (format "frame-return: ~v" (Frame-return frame)))
            (println (format "params: ~v" (Frame-params frame)))
            ; evalaute 'ensures' post conditions

            (printf "vc-asserts: ~v" (vc-asserts (vc)))
            
            (for/list ([en ensures])
                (assert (eval-contract-cond en frame))))))