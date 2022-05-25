#lang typed/racket

(provide parse-expr parse-stmt parse-fundef parse-type)
(provide Opt Some Some? Some-v None)
(provide
 NumExpr IdExpr ResultExpr ArrayLengthExpr ForallExpr BoolExpr BinOpExpr UnOpExpr NewArrayExpr MakeArrayExpr ArrayRefExpr BoolExpr BoolExpr?
 OldExpr IncStmt DecStmt RetStmt WhileStmt IfStmt IfStmt? AssignStmt AssignStmt? BeginStmt
 AnnoStmt Expr Expr? Type FunType ArrayType ArrayType-elem-type 
 ArrayType? FunType? Stmt Stmt? LVal LVal? RetStmt? WhileStmt? IncStmt? DecStmt?
 ArraySetStmt BeginStmt?
 CallExpr CallExpr? CallStmt CallStmt? Contract Contract?)

(provide BinOpExpr-left BinOpExpr-right BinOpExpr-op BinOp? UnOp UnOp?)
(provide Fundef Fundef? Fundef-id)

(provide Decl Decl-name Decl-typ Anno)
(require racket/set)

(struct (a) Some ([v : a]) #:transparent)
(struct None () #:transparent)
(define-type (Opt a) (U (Some a) None))

(define-type UnOp (U '! '~ 'neg))
(define-predicate UnOp? UnOp)

(define-type BinOp (U '+ '- '* '/ '% '<< '>>
    '< '> '>= '<= 'eq? 'ne? 'band 'xor 'bor 'and 'or))
(define-predicate BinOp? BinOp)
(define-type AsnOp (U
                    'set= 'set+= 'set-= 'set/=
                    'set*= 'set>>= 'set<<= 'set^= 'set&= 'set-bor= ))
(define-predicate AsnOp? AsnOp)

(define-type Validation (U 'invariant 'assert) )
(define-predicate Validation? Validation)

(define-type ContractKind (U 'requires 'ensures))
(define-predicate ContractKind? ContractKind)

(: keywords (Setof Symbol))
(define keywords (set 'if 'else 'while 'forall 'where 'length 'new-array 'array-set 'array-ref 'return '@old '@result))

; types
(define-type BoolType 'bool)
(define-predicate BoolType? BoolType)

(define-type IntType 'int)
(define-predicate IntType? IntType)

(define-type VoidType 'void)
(define-predicate VoidType? VoidType)

(struct FunType ([arg-types : (Listof Type)] [ret-type : Type]) #:transparent)
(struct ArrayType ([elem-type : Type]) #:transparent)

(define-type Type (U BoolType IntType VoidType FunType ArrayType))
(define-predicate Type? Type)

(define-type Vid Symbol)
(define-predicate Vid? Vid)
(struct IdExpr ([name : Symbol]) #:transparent)
(struct NumExpr ([val : Integer]) #:transparent)
(struct UnOpExpr ([op : UnOp] [expr : Expr]) #:transparent)
(struct BinOpExpr ([op : BinOp] [left : Expr] [right : Expr]) #:transparent)
(struct CallExpr ([name : Vid] [args : (Listof Expr)]) #:transparent)
(struct ArrayRefExpr ([arr : Expr] [idx : Expr]) #:transparent)
(struct ArrayLengthExpr ([arr : Expr]) #:transparent)

(define-type BoolExpr (U 'true 'false))
(define-predicate BoolExpr? BoolExpr)

(define-type Expr (U IdExpr NumExpr UnOpExpr BoolExpr BinOpExpr OldExpr ResultExpr CallExpr 
                    NewArrayExpr MakeArrayExpr ArrayRefExpr ArrayLengthExpr ForallExpr))

(define-predicate Expr? Expr)
(struct OldExpr ([exp : Expr]) #:transparent)

(struct NewArrayExpr ([typ : Type] [len : Expr]) #:transparent)
(struct MakeArrayExpr ([typ : Type] [vals : (Listof Expr)]) #:transparent)
(struct ForallExpr ([decls : (Listof Decl)] [where : Expr] [predicate : Expr]) #:transparent)

(define-type ResultExpr '@result)
(define-predicate ResultExpr? ResultExpr)

(struct Anno ([kind : Validation] [expr : Expr]) #:transparent)
(struct Contract ([kind : ContractKind] [expr : Expr]) #:transparent)
(struct Decl ([name : Vid] [typ : Type] [val : (Opt Expr)]) #:transparent)
(define-type DeclBlock (Listof Decl))
(define-predicate DeclBlock? DeclBlock)

(struct AssignStmt ([op : AsnOp] [target : LVal] [src : Expr]) #:transparent)
(struct IfStmt ([guard : Expr] [then : Stmt] [other : (Opt Stmt)]) #:transparent)
(struct WhileStmt ([guard : Expr] [body : Stmt]) #:transparent)
(struct RetStmt ([exp : (Opt Expr)]) #:transparent)
(struct CallStmt ([name : Vid] [args : (Listof Expr)]) #:transparent)
(struct BeginStmt ([decls : DeclBlock] [stmts : (Listof Stmt)]) #:transparent)
(struct AssertStmt ([exp : Expr]) #:transparent)
(struct IncStmt ([lv : LVal]) #:transparent)
(struct DecStmt ([lv : LVal]) #:transparent)
(struct ArraySetStmt ([arr : LVal] [idx : Expr] [val : Expr]) #:transparent)
(struct Fundef ([id : Symbol] [args : (Listof Decl)] [rtype : Type] [requires : (Listof Contract)] 
                [ensures : (Listof Contract)] [body : Stmt]) #:transparent)

(define (type-name? s) (memv s '(array)))

(define (valid-id? [s : Sexp])
  (and (symbol? s) (and (not 
                            (or (BoolExpr? s) (BinOp? s) (UnOp? s) 
                                (type-name? s) (Type? s) (AsnOp? s) 
                        (Validation? s) (ContractKind? s))) 
                        (not (set-member? keywords s)))))

(define-type LVal Vid)
(define-predicate LVal? LVal)

(define-type SimpleStmt (U AssignStmt IncStmt DecStmt ArraySetStmt))
(struct AnnoStmt ([anno : (Listof Anno)] [stmt : Stmt]) #:transparent)
(define-type Stmt (U SimpleStmt IfStmt WhileStmt BeginStmt
                     BeginStmt AssertStmt AnnoStmt CallStmt RetStmt))
(define-predicate Stmt? Stmt)

(: parse-expr (Sexp -> Expr))
(define (parse-expr sexp)
  (match sexp
    [(? exact-integer? i) (NumExpr i)]
    [(list (? BinOp? op) lht rht) (BinOpExpr op (parse-expr lht) (parse-expr rht))]
    [(list (? UnOp? op) e) (UnOpExpr op (parse-expr e))]
    [(? BoolExpr? b) b]
    [(? valid-id? (? symbol? id)) (IdExpr id)]
    [(? ResultExpr? r) r]
    [(list 'forall (list args ...) '#:where where-expr ': pred)
        (ForallExpr (parse-args args) (parse-expr where-expr) (parse-expr pred))]
    [(list 'new-array typ len-expr) (NewArrayExpr (parse-type typ) (parse-expr len-expr))]
    [(list 'make-array typ exprs ...) (MakeArrayExpr (parse-type typ) (map parse-expr (cast exprs (Listof Sexp))))]
    [(list 'array-ref arr i) (ArrayRefExpr (parse-expr arr) (parse-expr i))]
    [(list 'length expr) (ArrayLengthExpr (parse-expr expr))]
    [(list 'old e) (OldExpr (parse-expr e))]
    [(list (? valid-id? id) args ...) (CallExpr id (map parse-expr args))]
    [other (error 'bad-expr (format "~e" other))]))

(: type? (Sexp -> Boolean))
(define (type? sexp)
    (match sexp
        [(? Type? _) #t]
        [(list 'array (? type? t)) #t]
        [other #f]))

(: parse-type (Sexp -> Type))
(define (parse-type sexp)
    (match sexp
        [(? Type? t) t]
        [(list 'array t) (ArrayType (parse-type t))]
        [other (error 'invalid-type-name (format "invalid type ~a" sexp))]))

(: parse-decl (Sexp -> Decl))
(define (parse-decl s)
  (match s
    [(list (? valid-id? id) ': typ expr) (Decl id (parse-type typ) (Some (parse-expr expr)))]
    [(list (? valid-id? id) ': typ) (Decl id (parse-type typ) (None))]
    [other (error 'bad-decl (format "bad decl syntax ~v" s))]))

(: parse-validation (Validation Sexp -> Anno))
(define (parse-validation v s)
    (Anno v (parse-expr s)))

(: parse-contract (ContractKind Sexp -> Contract))
(define (parse-contract c s)
    (Contract c (parse-expr s)))

(: parse-anno-stmt ((Listof Validation) (Listof Sexp) Sexp -> AnnoStmt))
(define (parse-anno-stmt vs exps stmt)
    (AnnoStmt 
        (map parse-validation vs exps)
        (parse-stmt stmt)))

(: parse-stmt (Sexp -> Stmt))
(define (parse-stmt sexp)
  (match sexp
      [(list (? AsnOp? asnop) (? valid-id? lv) e) (AssignStmt asnop lv (parse-expr e))]
      [(list 'if g t e) (IfStmt (parse-expr g) (parse-stmt t) (Some (parse-stmt e)))]
      [(list 'if g t) (IfStmt (parse-expr g) (parse-stmt t) (None))]
      [(list 'while g b) (WhileStmt (parse-expr g) (parse-stmt b))]
      [(list 'return e) (RetStmt (Some (parse-expr e)))]
      [(list 'return) (RetStmt (None))]
      [(list 'begin (list 'declare decls ...) stmts ...) (BeginStmt
                                                   (map parse-decl decls)
                                                   (map parse-stmt stmts))]
      [(list 'begin stmts ...) (BeginStmt
                                          '()
                                           (map parse-stmt stmts))]
    [(list 'inc (? valid-id? lv)) (IncStmt lv)]
    [(list 'dec (? valid-id? lv)) (DecStmt lv)]
    [(list 'array-set (? valid-id? lv) idx val) (ArraySetStmt lv (parse-expr idx) (parse-expr val))]
    [(list (list (? Validation? v) e) ... s)    (parse-anno-stmt 
                                                (cast v (Listof Validation))
                                                (cast e (Listof Sexp)) s)]
    [(list (? valid-id? id) args ...) (CallStmt id (map parse-expr args))]
    [other (error 'bad-stmt (format "~e" sexp))]))

(: parse-args (Sexp -> (Listof Decl)))
(define (parse-args s)
    (match s
        [(list (list (? valid-id? v) ': t) ...) 
                (map (lambda ([v : Vid] [t : Type]) 
                    (Decl v t (None))) (cast v (Listof Vid)) (map parse-type (cast t (Listof Sexp))))]
        [other (error 'bad-arg-syntax (format "~e" s))]))


(: collect-contracts (-> (Listof Contract) (Pairof (Listof Contract) (Listof Contract))))
(define (collect-contracts contracts)
    (match contracts
        ['() (cons '() '())]
        [(cons (Contract v e) rst)
            (match-let
                ([(cons ens reqs) (collect-contracts rst)])
                (if (equal? v 'ensures)
                    (cons (cons (Contract v e) ens) reqs)
                    (cons ens (cons (Contract v e) reqs))))]))

(: parse-contracts (-> (Listof ContractKind) (Listof Sexp) (Pairof (Listof Contract) (Listof Contract))))
(define (parse-contracts kinds exprs)
    (match-let* 
        ([annos (map parse-contract kinds exprs)])
            (collect-contracts annos)))
        
(: parse-fundef (Sexp -> Fundef))
(define (parse-fundef s)
    (match s
        [(list 'fun (list (? valid-id? id) args ...) '-> rtype
            (list (? ContractKind? v) e) ... body)
                (match-let* 
                     ([(cons ensures requires) (parse-contracts (cast v (Listof ContractKind)) (cast e (Listof Sexp)))])
                    (Fundef id (parse-args args) (parse-type rtype) requires ensures (parse-stmt body)))]
        [(list 'fun (list (? valid-id? id) args ...) 
            (list (? ContractKind? v) e) ... body)
            (match-let* 
                    ([(cons ensures requires) (parse-contracts (cast v (Listof ContractKind)) (cast e (Listof Sexp)))])
                    (Fundef id (parse-args args) 'void requires ensures (parse-stmt body)))]
        [other (error 'bad-fundef (format "~e" s))]))