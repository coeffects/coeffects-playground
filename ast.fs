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
  | Number of float
  | Ident of string
  | QIdent of string
  | White of string

/// Specifies the kind of coeffect we want to display
[<RequireQualifiedAccess>]
type CoeffectKind = 
  | ImplicitParams 
  | PastValues
  | Embedded of CoeffectKind

type CoeffectMode =
  | None = 0
  | Flat = 1
  | Structural = 2

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
  | None 
  | Past of int
  | ImplicitParam of string * Type

/// Represents the type of mini-ML expressions
and [<RequireQualifiedAccess>] Type = 
  | Variable of string
  | Primitive of string
  | Func of (Coeffect * Coeffect) * Type * Type
  | Tuple of list<Type>
  // Translation target langauge-only
  | FlatComonad of Coeffect * Type
  | StructuralComonad of Coeffect list * Type

/// Represents a pattern of the coeffect language
[<RequireQualifiedAccess>]
type Pattern<'T> =
  | Var of string
  | Tuple of list<TypedPat<'T>>
  | QVar of string

/// Represents a pattern with a type annotation of generic type
and TypedPat<'T> =
  | TypedPat of 'T * Pattern<'T>  

type Annotation =
  | Flat of Coeffect
  | Structural of Coeffect list

/// Represents an expression of the coeffect language
[<RequireQualifiedAccess>]
type Expr<'T> = 
  | Fun of TypedPat<'T> * Typed<'T>
  | Let of TypedPat<'T> * Typed<'T> * Typed<'T>
  | App of Typed<'T> * Typed<'T>
  | Var of string
  | Number of float
  | Binary of string * Typed<'T> * Typed<'T>
  // Coeffect language-only
  | Prev of Typed<'T>
  | QVar of string
  // Translation target language-only
  | Builtin of string * Annotation list
  | Tuple of list<Typed<'T>>

/// Represents an expression with a type annotation of generic type
and Typed<'T> =
  | Typed of 'T * Expr<'T>

/// Types of variables in the context
type Vars = Map<string, Type>

/// Collected variables with structural coeffect information
type CoeffVars = Map<string, Coeffect * Type>

// ------------------------------------------------------------------------------------------------
// Helper fucntions for working with the AST
// ------------------------------------------------------------------------------------------------

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Type = 
  /// Recognizes functions of shape `T1 -> (T2 ... -> TN)`
  let rec (|Funcs|_|) t =
    match t with 
    | Type.Func((c1, c2), t1, Funcs(inputs, t2)) ->Some(((c1, c2), t1)::inputs, t2)
    | Type.Func((c1, c2), t1, t2) ->Some([(c1, c2), t1], t2)
    | _ -> None

/// Provides helper functions for working with `Expr<'T>` and `Typed<'T>` values
module Expr = 

  /// Recognizes a function with one or more parameters
  let rec (|Funs|_|) e = 
    match e with
    | Expr.Fun(pat, Typed(_, Funs(pats, body))) -> Some(pat::pats, body)
    | Expr.Fun(pat, body) -> Some([pat], body)
    | _ -> None

  /// Recognizes a let binding with optional (function) parameters
  let (|Lets|_|) e = 
    match e with
    | Expr.Let(pat, Typed(_, Funs(pats, assign)), body) -> Some(pat::pats, assign, body)
    | Expr.Let(pat, assign, body) -> Some([pat], assign, body)
    | _ -> None

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
      | Expr.Number(n) -> Expr.Number(n)
      | Expr.Let(pat, e1, e2) -> Expr.Let(mapTypePat f pat, mapType f e1, mapType f e2)
      | Expr.QVar(v) -> Expr.QVar(v)
      | Expr.Var(v) -> Expr.Var(v)
      | Expr.Tuple(es) -> Expr.Tuple(List.map (mapType f) es)
      | Expr.Builtin(s, annots) -> Expr.Builtin(s, annots)
    Typed(f t, e)

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Coeffect =
  /// Recognizes a close coeffect, i.e. not containing any variables
  let (|Closed|_|) c = 
    let rec isClosed = function
      | Coeffect.None | Coeffect.Past _ | Coeffect.ImplicitParam _ | Coeffect.Ignore | Coeffect.Use -> true
      | Coeffect.Merge(c1, c2) 
      | Coeffect.Split(c1, c2) 
      | Coeffect.Seq(c1, c2) -> isClosed c1 && isClosed c2
      | Coeffect.Variable _ -> false
    if isClosed c then Some(c) else None

module ExprShape = 
  /// A Leaf expression has no child expression while
  /// a Nested expression has sub-exporessions
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
    | Expr.Number _
    | Expr.Builtin _ -> Leaf(e)

  /// Recreate a nested expression of the kind specified by 
  /// `e` with child expressions specified by `args`.
  let recreate e args =
    match e, args with
    | Expr.Prev(_), [e] -> Expr.Prev(e)
    | Expr.App(_, _), [e1; e2] -> Expr.App(e1, e2)
    | Expr.Binary(op, _, _), [e1; e2] -> Expr.Binary(op, e1, e2)
    | Expr.Fun(pats, _), [e] -> Expr.Fun(pats, e)
    | Expr.Number(n), _ -> Expr.Number(n)
    | Expr.Let(pat, _, _), [e1; e2] -> Expr.Let(pat, e1, e2)
    | Expr.QVar(v), _ -> Expr.QVar(v)
    | Expr.Var(v), _ -> Expr.Var(v)
    | Expr.Tuple(_), es -> Expr.Tuple(es)
    | Expr.Builtin(s, a), _ -> Expr.Builtin(s, a)
    | _ -> failwith "<strong>Internal error.</strong><br /> Invalid expression shape in <code>ExprShape.recreate</code>"