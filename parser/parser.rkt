#lang typed/racket

(provide parse-expr parse-stmt parse-fundef)
(provide Opt Some None)
(provide
 NumExpr IdExpr ResultExpr BoolExpr BinOpExpr UnOpExpr BoolExpr
 OldExpr IncStmt DecStmt RetStmt WhileStmt IfStmt AssignStmt BeginStmt
 AnnoStmt Expr Type Stmt)
(provide BinOpExpr-left BinOpExpr-right BinOpExpr-op)
(provide Fundef)

(provide Decl Anno)
(require racket/set)

(struct (a) Some ([v : a]) #:transparent)
(struct None () #:transparent)
(define-type (Opt a) (U (Some a) None))

(define-type UnOp (U '! '~ '-))
(define-predicate UnOp? UnOp)

(define-type BinOp (U '+ '- '* '/ '% '<< '>>
    '< '> '>= '<= 'eq? 'ne? 'band 'xor 'bor 'and 'or))
(define-predicate BinOp? BinOp)
(define-type AsnOp (U
                    'set= 'set+= 'set-= 'set
                    'set*= 'set-= 'set>>= 'set<<= 'set^= 'set&= 'set-bor= ))
(define-predicate AsnOp? AsnOp)

(define-type Validation (U 'requires 'ensures 'invariant 'assert) )
(define-predicate Validation? Validation)

(: keywords (Setof Symbol))
(define keywords (set 'if 'else 'while 'return '@old '@result))

; types
(define-type BoolType 'bool)
(define-type IntType 'int)
(define-type VoidType 'void)
(define-type Type (U BoolType IntType VoidType))
(define-predicate Type? Type)


(define-type Vid Symbol)
(define-predicate Vid? Vid)
(struct IdExpr ([name : Symbol]) #:transparent)
(struct NumExpr ([val : Integer]) #:transparent)
(struct UnOpExpr ([op : UnOp] [expr : Expr]) #:transparent)
(struct BinOpExpr ([op : BinOp] [left : Expr] [right : Expr]) #:transparent)
(define-type BoolExpr (U 'true 'false))
(define-predicate BoolExpr? BoolExpr)

(define-type Expr (U IdExpr NumExpr UnOpExpr BoolExpr BinOpExpr OldExpr ResultExpr))
(struct OldExpr ([exp : Expr]) #:transparent)
(define-type ResultExpr '@result)
(define-predicate ResultExpr? ResultExpr)

(struct Anno ([kind : Validation] [expr : Expr]) #:transparent)
(struct Decl ([name : Vid] [typ : Type] [val : (Opt Expr)]) #:transparent)
(define-type DeclBlock (Listof Decl))
(define-predicate DeclBlock? DeclBlock)

(struct AssignStmt ([op : AsnOp] [target : LVal][src : Expr]) #:transparent)
(struct IfStmt ([guard : Expr] [then : Stmt] [other : (Opt Stmt)]) #:transparent)
(struct WhileStmt ([guard : Expr] [body : Stmt]) #:transparent)
(struct RetStmt ([exp : (Opt Expr)]) #:transparent)
(struct BeginStmt ([decls : DeclBlock] [stmts : (Listof Stmt)]) #:transparent)
(struct AssertStmt ([exp : Expr]) #:transparent)
(struct IncStmt ([lv : LVal]) #:transparent)
(struct DecStmt ([lv : LVal]) #:transparent)
(struct Fundef ([id : Symbol] [args : (Listof Decl)] [rtype : Type] [body : Stmt])
    #:transparent)

(define (valid-id? [s : Sexp])
  (and (symbol? s) (and (not (or (BoolExpr? s) (BinOp? s) (UnOp? s) (Type? s) (AsnOp? s) (Validation? s))
            ) (not (set-member? keywords s)))))

(define-type LVal Vid)

(define-type SimpleStmt (U AssignStmt IncStmt DecStmt))
(struct AnnoStmt ([anno : (Listof Anno)] [stmt : Stmt]) #:transparent)
(define-type Stmt (U SimpleStmt IfStmt WhileStmt BeginStmt
                     BeginStmt AssertStmt AnnoStmt RetStmt))

(: parse-expr (Sexp -> Expr))
(define (parse-expr sexp)
  (match sexp
    [(? exact-integer? i) (NumExpr i)]
    [(list (? BinOp? op) lht rht) (BinOpExpr op (parse-expr lht) (parse-expr rht))]
    [(list (? UnOp? op) e) (UnOpExpr op (parse-expr e))]
    [(? BoolExpr? b) b]
    [(? valid-id? (? symbol? id)) (IdExpr id)]
    [(? ResultExpr? r) r]
    [(list 'old e) (OldExpr (parse-expr e))]
    [other (error 'bad-expr (format "~e" other))]))

(: parse-decl (Sexp -> Decl))
(define (parse-decl s)
  (match s
    [(list (? valid-id? id) ': (? Type? typ) exp) (Decl id typ (Some (parse-expr exp)))]
    [(list (? valid-id? id) ': (? Type? typ)) (Decl id typ (None))]
    [other (error 'bad-decl (format "bad decl syntax ~v" s))]))

(: parse-validation (Validation Sexp -> Anno))
(define (parse-validation v s)
    (Anno v (parse-expr s)))

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
    [(list (list (? Validation? v) e) ... s) (parse-anno-stmt 
                                                (cast v (Listof Validation))
                                                (cast e (Listof Sexp)) s)]
    [other (error 'bad-stmt (format "~e" sexp))]))

(: parse-args (Sexp -> (Listof Decl)))
(define (parse-args s)
    (match s
        [(list (list (? valid-id? v) ': (? Type? t)) ...) 
                (map (lambda ([v : Vid] [t : Type]) 
                    (Decl v t (None))) (cast v (Listof Vid)) (cast t (Listof Type)))]
        [other (error 'bad-arg-syntax (format "~e" s))]))

(: parse-fundef (Sexp -> Fundef))
(define (parse-fundef s)
    (match s
        [(list 'fun (list (? valid-id? id) args ...) '-> (? Type? rtype) body)
            (Fundef id (parse-args args) rtype (parse-stmt body))]
        [(list 'fun (list (? valid-id? id) args ...) body)
            (Fundef id (parse-args args) 'void (parse-stmt body))]
        [other (error 'bad-fundef (format "~e" s))]))