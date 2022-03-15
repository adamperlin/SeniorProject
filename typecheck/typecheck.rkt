#lang typed/racket

(require "../parser/parser.rkt")

(provide TypeEnv typecheck-expr typecheck-stmt lookup typecheck-function
    typecheck-program
    check-return-paths)

(define-type TypeEnv (HashTable Symbol Type))

(: add-binding (TypeEnv Decl -> TypeEnv))
(define (add-binding tenv decl)
    (match-let 
        ([(Decl name typ _) decl])
        (hash-set tenv name typ)))

(define binop-types (hash
    '> '(int . bool)
    '< '(int . bool)
    '>= '(int . bool)
    '<= '(int . bool)
    '>> '(int . int)
    '<< '(int . int)
    '+   '(int . int)
    '- '(int . int)
    '* '(int . int)
    '/ '(int . int)
    '% '(int . int)
    'band '(int . int)
    'bor '(int . int)
    'xor '(int . int)
    'and '(bool . bool)
    'or '(bool . bool)
    '! '(bool . bool)
))

(define unop-types (hash
    '! '(bool . bool)
    'neg '(int . int)
    '~ '(int . int)))

(: typecheck-binop(BinOpExpr TypeEnv -> Type))
(define (typecheck-binop expr type-env) 
        (match-let* 
            ([(BinOpExpr op left right) expr]
             [tleft (typecheck-expr left type-env)]
             [tright (typecheck-expr right type-env)])
             (unless (equal? tleft tright)
                (error 'bad-operand-type (format "bad operand type for ~v: ~v ~v" op tleft tright)))
            (if (or (equal? op 'eq?) (equal? op 'ne?))
                'bool
                (match-let
                    ([(cons arg-t ret-t) (hash-ref binop-types (BinOpExpr-op expr))])
                    (unless (equal? tleft arg-t)
                        (error 'bad-operand-type (format "bad operand type for ~v: ~v ~v" op tleft tright)))
                        ret-t))))

(: typecheck-unop (UnOpExpr TypeEnv -> Type))
(define (typecheck-unop expr type-env)
    (match-let*
        ([(UnOpExpr op ex) expr]
        [texp (typecheck-expr ex type-env)]
        [(cons arg-t ret-t) (hash-ref unop-types op)])
        (unless (equal? texp arg-t)
            (error 'bad-operand-type (format "bad operand type for ~v: ~v" op texp)))
        ret-t))

(: typecheck-result-expr (TypeEnv -> Type))
(define (typecheck-result-expr type-env)
    (when (not (hash-has-key? type-env '_ret))
        (error 'invalid-state (format "type environment must contain value for ~v" '_ret)))
    ; a result expression refers to the return value of the function,
    ; thus it has the type of the function return value.
    ; we keep a default entry _ret in the type environment to allow for this
    (hash-ref type-env '_ret))

(: typecheck-call (Symbol (Listof Expr) TypeEnv -> Type))
(define (typecheck-call id args type-env)
    (match-let*
        ([type (lookup type-env id)])
        (unless (FunType? type)
            (error (format "cannot call non-function ~v" id)))
        (match-let 
            ([(FunType want-args ret) type]
             [arg-types (map (lambda ([e : Expr]) (typecheck-expr e type-env)) args)])
             (when (not (equal? arg-types want-args))
                (error 'bad-call (format "argument type mismatch: got ~v, expecting ~v" arg-types want-args)))
            ret)))

(: typecheck-call-expr (CallExpr TypeEnv -> Type))
(define (typecheck-call-expr call-expr type-env)
    (match-let
        ([(CallExpr id args) call-expr])
        (typecheck-call id args type-env)))

(: typecheck-call-stmt (CallStmt TypeEnv -> Void))
(define (typecheck-call-stmt call-stmt type-env)
    (match-let
        ([(CallStmt id args) call-stmt])
        (begin 
            (typecheck-call id args type-env)
            (void))))

; typechecking expressions
(: typecheck-expr (Expr TypeEnv -> Type))
(define (typecheck-expr expr type-env)
    (match expr
        [(IdExpr id) (lookup type-env id)]
        [(NumExpr n) 'int]
        [(or 'true 'false) 'bool]
        [(BinOpExpr _ _ _) (typecheck-binop expr type-env)]
        [(UnOpExpr _ _) (typecheck-unop expr type-env)]
        [(OldExpr ex) (typecheck-expr ex type-env)]
        [(CallExpr _ _) (typecheck-call-expr expr type-env)]
        ['@result (typecheck-result-expr type-env)]))

(: bind-opt (All (A B) (-> (A -> (Opt B)) (Opt A) (Opt B))))
(define (bind-opt fn opt)
    (match opt 
        [(Some a) (fn a)]
        [(None) (None)]))

(: typecheck-if-stmt (IfStmt TypeEnv -> Void))
(define (typecheck-if-stmt if-stmt type-env)
    (match-let*
        ([(IfStmt g t e) if-stmt]
         [guard-t (typecheck-expr g type-env)])
         (unless (equal? guard-t 'bool)
            (error 'bad-if-cond (format "expecting if condition to be bool in ~v" g)))
        (typecheck-stmt t type-env) 
        (bind-opt (lambda ([s : Stmt]) (typecheck-stmt s type-env) (None)) e)
        (void)))

(: typecheck-while-stmt (WhileStmt TypeEnv -> Void))
(define (typecheck-while-stmt while-stmt type-env)
    (match-let*
        ([(WhileStmt g b) while-stmt]
        [guard-t (typecheck-expr g type-env)])
        (unless (equal? guard-t 'bool)
            (error 'bad-while-cond (format "expecting while condition to be bool in ~v" g)))
        (typecheck-stmt b type-env)))

(define assign-op-types (hash
                        'set+= '(int . int)
                        'set-= '(int . int)
                        'set*= '(int . int) 
                        'set-= '(int . int)
                        'set>>= '(int . int) 
                        'set<<= '(int . int)
                        'set^= '(int . int)
                        'set&= '(int . int) 
                        'set-bor= '(int . int)))

(: lookup (TypeEnv Symbol -> Type))
(define (lookup type-env id)
    (unless (hash-has-key? type-env id)
        (error 'unknown-id (format "unknown identifier ~v" id)))
    (hash-ref type-env id))

(: typecheck-assign-stmt (AssignStmt TypeEnv -> Void))
(define (typecheck-assign-stmt assign-stmt type-env)
    (match-let*
        ([(AssignStmt op lval src) assign-stmt]
        [lval-t (lookup type-env lval)]
        [src-t (typecheck-expr src type-env)])
        (when (not (equal? lval-t src-t))
                (error 'bad-assign (format "assignment type mismatch: ~v ~v ~v" op lval-t src-t)))
        (unless (equal? op 'set=)
            (match-let
                ([(cons expect-lval-t expect-src-t) (hash-ref assign-op-types op)])
                (when (not (or (equal? expect-lval-t lval-t) (equal? expect-src-t src-t)))
                    (error 'bad-assign (format "assignment type mismatch: ~v ~v ~v" op lval-t src-t)))))))

(: typecheck-inc-stmt (IncStmt TypeEnv -> Void))
(define (typecheck-inc-stmt inc-stmt type-env)
    (match-let* 
        ([(IncStmt lval) inc-stmt]
         [lval-t (lookup type-env lval)])
         (unless (equal? lval-t 'int)
            (error 'bad-inc (format "cannot use operator inc on type ~v in ~v" lval-t inc-stmt)))))

(: typecheck-dec-stmt (DecStmt TypeEnv -> Void))
(define (typecheck-dec-stmt dec-stmt type-env)
    (match-let* 
        ([(DecStmt lval) dec-stmt]
         [lval-t (lookup type-env lval)])
         (unless (equal? lval-t 'int)
            (error 'bad-dec (format "cannot use operator dec on type ~v in ~v" lval-t dec-stmt)))))

(: maybe (All (A) ((Opt A) A -> A)))
(define (maybe opt default)
    (match opt
        [(Some a) a]
        [(None) default]))

(: typecheck-begin-stmt (BeginStmt TypeEnv -> Void))
(define (typecheck-begin-stmt begin-stmt type-env)
    (match-let*
        ([(BeginStmt decls stmts) begin-stmt]
        [new-env (foldl (lambda ([decl : Decl] [env : TypeEnv]) (add-binding env decl)) type-env decls)])
        (for/list: : (Listof Void) ([stmt stmts])
            (typecheck-stmt stmt new-env)))
    (void))

(: typecheck-anno (Anno TypeEnv -> Void))
(define (typecheck-anno anno type-env)
    (match-let*
        ([(Anno v con) anno]
        [con-t (typecheck-expr con type-env)])
        (unless (equal? con-t 'bool)
            (error 'bad-annotation 
                (format "expected annotation ~v to have type bool, got ~v" anno con-t)))))

(: typecheck-function-contract (Contract TypeEnv -> Void))
(define (typecheck-function-contract anno type-env)
    (match-let*
        ([(Contract c con) anno]
        [con-t (typecheck-expr con type-env)])
        (unless (equal? con-t 'bool)
            (error 'bad-contract 
                (format "expected contract ~v to have type bool, got ~v" anno con-t)))))

(: fun-type (Fundef -> FunType))
(define (fun-type fundef)
    (match-let
        ([(Fundef _ args rtype _ _ _) fundef])
        (FunType (map Decl-typ args) rtype)))

(: typecheck-function (Fundef TypeEnv -> TypeEnv))
(define (typecheck-function fundef top-env)
    (match-let*
        ([(Fundef id args rtype reqs ens body) fundef]
        [new-env1 (foldl (lambda ([decl : Decl] [env : TypeEnv]) (add-binding env decl)) top-env args)]
        [new-env2 (add-binding new-env1 (Decl '_ret rtype (None)))]
        [fun-binding (Decl id (fun-type fundef) (None))]
        [new-env3 (add-binding new-env2 fun-binding)]) 
        (for/list: : (Listof Void) ([req reqs])
            (typecheck-function-contract req new-env2))
        (for/list: : (Listof Void) ([e ens])
            (typecheck-function-contract e new-env2))
        (typecheck-stmt body new-env2)
        (check-return-paths fundef)
        (add-binding top-env fun-binding)))

(: check-return-path (Stmt -> Boolean))
(define (check-return-path stmt)
    (match stmt
        [(AssignStmt _ _ _) #f]
        [(RetStmt _) #t]
        [(IfStmt _ t e) 
            (match e
                [(Some els) (and (check-return-path t) (check-return-path els))]
                [other #f])]
        [(WhileStmt _ _) #f]
        [(IncStmt _) #f]
        [(DecStmt _) #f]
        [(BeginStmt _ stmts)
            (foldl (lambda ([t : Boolean] [cur : Boolean]) (or t cur)) #f (map check-return-path stmts))]
        [(AnnoStmt _ s) (check-return-path s)]))

(: check-return-paths (Fundef -> Void))
(define (check-return-paths fundef)
    (match-let*
        ([(Fundef id args rtype _ _ body) fundef])
        (unless (check-return-path body)
            (error 'incomplete-return-paths (format "incomplete return paths in function ~v" id)))))

(: typecheck-anno-stmt (AnnoStmt TypeEnv -> Void))
(define (typecheck-anno-stmt anno-stmt type-env)
    (match-let*
        ([(AnnoStmt annos stmt) anno-stmt])
        (for/list: : (Listof Void) ([anno annos])
            (typecheck-anno anno type-env))
        (typecheck-stmt stmt type-env)))

(: typecheck-ret-stmt (RetStmt TypeEnv -> Void))
(define (typecheck-ret-stmt ret-stmt type-env)
    (match-let*
        ([(RetStmt maybe-e) ret-stmt]
        [maybe-ret-t (bind-opt (lambda ([e : Expr]) (Some (typecheck-expr e type-env))) maybe-e)])
        (bind-opt (lambda ([rt : Type])
                    (let 
                        ([ret-t (lookup type-env '_ret)])
                        (unless (equal? rt ret-t)
                            (error 
                                (format "cannot return type ~v from function of type ~v" rt ret-t))) 
                                    (None))) maybe-ret-t)) (void))

(: typecheck-stmt (Stmt TypeEnv -> Void))
(define (typecheck-stmt stmt type-env)
    (match stmt
        [(IfStmt _ _ _) (typecheck-if-stmt stmt type-env)]
        [(WhileStmt g b) (typecheck-while-stmt stmt type-env)]
        [(AssignStmt _ _ _) (typecheck-assign-stmt stmt type-env)]
        [(IncStmt lval) (typecheck-inc-stmt stmt type-env)]
        [(DecStmt lval) (typecheck-dec-stmt stmt type-env)]
        [(RetStmt _) (typecheck-ret-stmt stmt type-env)]
        [(BeginStmt decls stmts) (typecheck-begin-stmt stmt type-env)]
        [(AnnoStmt _ _) (typecheck-anno-stmt stmt type-env)]
        [(CallStmt _ _) (typecheck-call-stmt stmt type-env)]))

(: typecheck-program ((Listof Fundef) -> Void))
(define (typecheck-program defs)
    (define top-type-env (ann (hash) TypeEnv))
    (define final-env (foldl (lambda ([f : Fundef] [top-env : TypeEnv])
                    (typecheck-function f top-env)) top-type-env defs))
    (void))