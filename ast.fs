// ------------------------------------------------------------------------------------------------
// The AST defines types for tokens, patterns and expressions
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Ast

/// Represents tokens of the coeffect langauge 
[<RequireQualifiedAccess>]
type Token = 
  | RParen
  | Equals
  | LParen
  | Fun
  | Arrow
  | Let
  | In
  | Prev
  | Comma
  | Operator of string
  | Integer of int
  | Ident of string
  | QIdent of string
  | White of string

/// Specifies the kind of coeffect we want to display
[<RequireQualifiedAccess>]
type CoeffectKind = 
  | ImplicitParams 
  | PastValues

[<RequireQualifiedAccess>]
type Coeffect = 
  // Flat coeffect algebra
  | Variable of string
  | Use 
  | Ignore
  | Merge of Coeffect * Coeffect
  | Split of Coeffect * Coeffect
  | Seq of Coeffect * Coeffect
  // Special coeffects for concrete applications
  | Past of int
  | ImplicitParam of string * Type

/// Represents the type of mini-ML expressions
and [<RequireQualifiedAccess>] Type = 
  | Variable of string
  | Primitive of string
  | Func of Coeffect * Type * Type
  | Tuple of list<Type>
  // Translation target langauge-only
  | Comonad of Coeffect * Type

/// Represents a pattern of the coeffect language
[<RequireQualifiedAccess>]
type Pattern<'T> =
  | Var of string
  | Tuple of list<TypedPat<'T>>
  | QVar of string

/// Represents a pattern with a type annotation of generic type
and TypedPat<'T> =
  | TypedPat of 'T * Pattern<'T>  

/// Represents an expression of the coeffect language
[<RequireQualifiedAccess>]
type Expr<'T> = 
  | Fun of TypedPat<'T> * Typed<'T>
  | Let of TypedPat<'T> * Typed<'T> * Typed<'T>
  | App of Typed<'T> * Typed<'T>
  | Var of string
  | Integer of int
  | Binary of string * Typed<'T> * Typed<'T>
  // Coeffect language-only
  | Prev of Typed<'T>
  | QVar of string
  // Translation target language-only
  | Builtin of string * Coeffect list
  | Tuple of list<Typed<'T>>

/// Represents an expression with a type annotation of generic type
and Typed<'T> =
  | Typed of 'T * Expr<'T>

/// Types of variables in the context
type Vars = Map<string, Type>

// ------------------------------------------------------------------------------------------------
// Helper fucntions for working with the AST
// ------------------------------------------------------------------------------------------------

/// Provides helper functions for working with `Expr<'T>` and `Typed<'T>` values
module Expr = 

  /// Transform the type annotations in the specified pattern using the provided function
  let rec mapTypePat f (TypedPat(t, p)) =
    let p = 
      match p with
      | Pattern.Tuple(pats) -> Pattern.Tuple(List.map (mapTypePat f) pats)
      | Pattern.Var v -> Pattern.Var v
      | Pattern.QVar v -> Pattern.QVar v
    TypedPat(f t, p)

  /// Transform the type annotations in the specified expression using the provided function
  let rec mapType f (Typed(t, e)) =
    let e = 
      match e with
      | Expr.Prev(e) -> Expr.Prev(mapType f e)
      | Expr.App(e1, e2) -> Expr.App(mapType f e1, mapType f e2)
      | Expr.Binary(op, e1, e2) -> Expr.Binary(op, mapType f e1, mapType f e2)
      | Expr.Fun(pats, e) -> Expr.Fun(mapTypePat f pats, mapType f e)
      | Expr.Integer(n) -> Expr.Integer(n)
      | Expr.Let(pat, e1, e2) -> Expr.Let(mapTypePat f pat, mapType f e1, mapType f e2)
      | Expr.QVar(v) -> Expr.QVar(v)
      | Expr.Var(v) -> Expr.Var(v)
      | Expr.Tuple(es) -> Expr.Tuple(List.map (mapType f) es)
      | Expr.Builtin(s, annots) -> Expr.Builtin(s, annots)
    Typed(f t, e)

module ExprShape = 
  let (|Leaf|Nested|) e =
    match e with
    | Expr.Binary(_, e1, e2)
    | Expr.Let(_, e1, e2)
    | Expr.App(e1, e2) -> Nested(e, [e1; e2])
    | Expr.Prev(e1)
    | Expr.Fun(_, e1)
    | Expr.Prev e1 -> Nested(e, [e1])
    | Expr.Tuple es -> Nested(e, es)
    | Expr.QVar _
    | Expr.Var _
    | Expr.Integer _
    | Expr.Builtin _ -> Leaf(e)

  let recreate e args =
    match e, args with
    | Expr.Prev(_), [e] -> Expr.Prev(e)
    | Expr.App(_, _), [e1; e2] -> Expr.App(e1, e2)
    | Expr.Binary(op, _, _), [e1; e2] -> Expr.Binary(op, e1, e2)
    | Expr.Fun(pats, _), [e] -> Expr.Fun(pats, e)
    | Expr.Integer(n), _ -> Expr.Integer(n)
    | Expr.Let(pat, _, _), [e1; e2] -> Expr.Let(pat, e1, e2)
    | Expr.QVar(v), _ -> Expr.QVar(v)
    | Expr.Var(v), _ -> Expr.Var(v)
    | Expr.Tuple(_), es -> Expr.Tuple(es)
    | Expr.Builtin(s, a), _ -> Expr.Builtin(s, a)
    | _ -> failwith "Invalid expression shape"