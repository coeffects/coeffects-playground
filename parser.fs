// ------------------------------------------------------------------------------------------------
// Parser for a mini-ML langauge - turns list<Token> into Expr
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Parser

open Coeffects.Parsec
open Coeffects.Ast
open Coeffects.Lexer

// Parsing of patterns
let pattern =
  choose (function Token.Ident id -> Some(Pattern.Var id) | _ -> None) <|>
  choose (function Token.QIdent id -> Some(Pattern.QVar id) | _ -> None)
  
let patterns = oneOrMore pattern
  
// Parsing of simple expressions that correspond to tokens
let token tok = pred ((=) tok)

let var = 
  choose (function Token.Ident id -> Some(Expr.Var id) | _ -> None)
let qvar = 
  choose (function Token.QIdent id -> Some(Expr.QVar id) | _ -> None)
let integer = 
  choose (function Token.Integer n -> Some(Expr.Integer n) | _ -> None)
let op = 
  choose (function Token.Operator s -> Some s | _ -> None)

// Parsing of function applications and operators
type Associativity = Left | Right

let precedence = function
  | "+" | "-" -> 1, Left
  | "*" | "/" -> 2, Left
  | "^" -> 3, Right
  | _ -> failwith "Invalid"

/// Represnts a sequence of expressions separated by binary operators
/// (e.g. 'f x + 1 * 2 / g y' has 4 expressions separated by 3 operators)
type OpExpr = OpExpr of Expr * option<string * OpExpr>

/// Turn 'OpExpr' into a parsed 'Expr' using the "Precedence climbing method"
/// (see https://en.wikipedia.org/wiki/Operator-precedence_parser)
let rec buildExpr minPrec (OpExpr(app, next)) = 
  let rec loop result next = 
    match next with 
    | Some(op, next) when fst (precedence op) >= minPrec ->
        let prec, assoc = precedence op
        let nextMinPrec = 
          if assoc = Left then prec + 1 else prec
        let rhs, next = buildExpr nextMinPrec next
        let result = Expr.Binary(op, result, rhs)               
        loop result next
    | _ -> result, next      
  loop app next

/// Parse '<term> <term> .. <term>' representing function application
let rec apps () = 
  oneOrMore (term ()) |> map (fun t -> 
      List.tail t |> List.fold (fun st v -> Expr.App(st, v)) (List.head t))

/// Parse '<apps> <op> <apps> .. <apps>' representing expression with operators
and opExpr () = delay (fun () ->
  apps() <*> (optional (op <*> opExpr ()))
  |> map (fun (hd, tl) -> OpExpr(hd, tl)) )

/// Parse the same as 'opExpr' and then turn it into 'Expr' using 'buildExpr'
and expr () = 
  opExpr () |> map (buildExpr 1 >> fst)

/// Parse an expression wrapped in brackets
and bracketed () = delay (fun () ->
  ( token Token.LParen <*>
    expr () <*>
    token Token.RParen )
  |> map (fun ((_, e), _) -> e) )

/// Parse let binding of the form 'let <pat> = <expr> in <expr>'
and binding () = delay (fun () ->
  ( token Token.Let <*>
    pattern <*>
    token Token.Equals <*>
    expr () <*>
    token Token.In <*>
    expr () )
  |> map (fun (((((_, pat), _), assign), _), body) ->
    Expr.Let(pat, assign, body)) )

/// Parse a function of the form 'fun <pat> .. <pat> -> <expr>'
and func () = delay (fun () ->
  ( token Token.Fun <*>
    patterns <*>
    token Token.Arrow <*>
    expr () )
  |> map (fun (((_, pats), _), body) -> 
    Expr.Fun(pats, body) ))

/// Parse a term (this handles most of the usual expressions)
and term () = delay (fun () ->
  func () <|>
  integer <|>
  var <|> 
  qvar <|>
  binding () <|>
  bracketed () )
