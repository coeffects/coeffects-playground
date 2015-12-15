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
  | Operator of string
  | Integer of int
  | Ident of string
  | QIdent of string
  | White of string

/// Represents a pattern of the coeffect language
[<RequireQualifiedAccess>]
type Pattern =
  | Var of string
  | QVar of string
  
/// Represents an expression of the coeffect language
[<RequireQualifiedAccess>]
type Expr<'T> = 
  | Fun of Pattern * Typed<'T>
  | Let of Pattern * Typed<'T> * Typed<'T>
  | App of Typed<'T> * Typed<'T>
  | Prev of Typed<'T>
  | Var of string
  | QVar of string
  | Integer of int
  | Binary of string * Typed<'T> * Typed<'T>

/// Represents an expression with a type annotation of generic type
and Typed<'T> =
  | Typed of 'T * Expr<'T>

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

/// Types of variables in the context
type Vars = Map<string, Type>

// ------------------------------------------------------------------------------------------------
// Helper fucntions for working with the AST
// ------------------------------------------------------------------------------------------------

/// Provides helper functions for working with `Expr<'T>` and `Typed<'T>` values
module Expr = 

  /// Transform the type annotations in the specified expression using the provided function
  let rec mapType f (Typed.Typed(t, e)) =
    let e = 
      match e with
      | Expr.Prev(e) -> Expr.Prev(mapType f e)
      | Expr.App(e1, e2) -> Expr.App(mapType f e1, mapType f e2)
      | Expr.Binary(op, e1, e2) -> Expr.Binary(op, mapType f e1, mapType f e2)
      | Expr.Fun(pats, e) -> Expr.Fun(pats, mapType f e)
      | Expr.Integer(n) -> Expr.Integer(n)
      | Expr.Let(pat, e1, e2) -> Expr.Let(pat, mapType f e1, mapType f e2)
      | Expr.QVar(v) -> Expr.QVar(v)
      | Expr.Var(v) -> Expr.Var(v)
    Typed.Typed(f t, e)

