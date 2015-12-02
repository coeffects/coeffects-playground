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
type Expr = 
  | Fun of list<Pattern> * Expr
  | Let of Pattern * Expr * Expr
  | App of Expr * Expr
  | Var of string
  | QVar of string
  | Integer of int
  | Binary of string * Expr * Expr

