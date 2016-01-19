// ------------------------------------------------------------------------------------------------
// Parser for a mini-ML langauge - turns list<Token> into Expr
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Parser

open Coeffects
open Coeffects.Parsec
open Coeffects.Ast
open Coeffects.Lexer

// Parsing of simple expressions that correspond to tokens
let token tok = pred ((=) tok)

let var = 
  choose (function Token.Ident id -> Some(Typed.Typed((), Expr.Var id)) | _ -> None)
let qvar = 
  choose (function Token.QIdent id -> Some(Typed.Typed((), Expr.QVar id)) | _ -> None)
let integer = 
  choose (function Token.Number n -> Some(Typed.Typed((), Expr.Number n)) | _ -> None)
let op = 
  choose (function Token.Operator s -> Some s | _ -> None)

// Parsing of patterns
let patIdent =
  ( choose (function Token.Ident id -> Some(Pattern.Var id) | _ -> None) <|>
    choose (function Token.QIdent id -> Some(Pattern.QVar id) | _ -> None) )
  |> map (fun p -> TypedPat((), p))

let rec patNested () = 
  ( token Token.LParen <*>
    pattern () <*>
    token Token.RParen )
  |> map (fun ((_, p), _) -> p)

and patOneOrTuple () = 
  ( patIdent <*>
    zeroOrMore (token Token.Comma <*> pattern ()) )
  |> map (fun (p, ps) -> 
    match ps with 
    | [] -> p
    | ps -> TypedPat((), Pattern.Tuple(p :: (List.map snd ps))) )
  
and pattern () = delay (fun () ->
  patNested () <|> patOneOrTuple ())
  

// Parsing of function applications and operators
type Associativity = Left | Right

let precedence = function
  | "+" | "-" -> 1, Left
  | "*" | "/" -> 2, Left
  | "^" -> 3, Right
  | _ -> Errors.unexpected "Invalid operator name in <code>Parser.precedence</code>."

/// Represnts a sequence of expressions separated by binary operators
/// (e.g. 'f x + 1 * 2 / g y' has 4 expressions separated by 3 operators)
type OpExpr = OpExpr of Typed<unit> * option<string * OpExpr>

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
        let result = Typed.Typed((), Expr.Binary(op, result, rhs))
        loop result next
    | _ -> result, next      
  loop app next

/// Parse '<term> <term> .. <term>' representing function application
let rec apps () = 
  oneOrMore (term ()) |> map (fun t -> 
      List.tail t |> List.fold (fun st v -> Typed.Typed((), Expr.App(st, v))) (List.head t))

/// Parse '<apps> <op> <apps> .. <apps>' representing expression with operators
and opExpr () = delay (fun () ->
  apps() <*> (optional (op <*> opExpr ()))
  |> map (fun (hd, tl) -> OpExpr(hd, tl)) )

/// Parse the same as 'opExpr' and then turn it into 'Expr' using 'buildExpr'
and expr () = 
  ( opExpr () <*> 
    zeroOrMore (token Token.Comma <*> opExpr ()) )
  |> map (fun (e, es) ->
      let exprs = e::(List.map snd es) |> List.map (buildExpr 1 >> fst)
      match exprs with 
      | [e] -> e
      | es -> Typed((), Expr.Tuple(es)) )

/// Parse an expression wrapped in brackets
and bracketed () = delay (fun () ->
  ( token Token.LParen <*>
    expr () <*>
    token Token.RParen )
  |> map (fun ((_, e), _) -> e) )

/// Parse let binding of the form 'let <pat> = <expr> in <expr>'
and binding () = delay (fun () ->
  ( token Token.Let <*>
    zeroOrMore(pattern ()) <*>
    token Token.Equals <*>
    expr () <*>
    token Token.In <*>
    expr () )
  |> map (fun (((((_, pats), _), assign), _), body) ->
    let pat, pats = List.head pats, List.rev (List.tail pats)
    let assign = pats |> List.fold (fun assign pat -> Typed.Typed((), Expr.Fun(pat, assign))) assign
    Typed.Typed((), Expr.Let(pat, assign, body))) )

/// Parse a function of the form 'fun <pat> .. <pat> -> <expr>'
and func () = delay (fun () ->
  ( token Token.Fun <*>
    oneOrMore (pattern ()) <*>
    token Token.Arrow <*>
    expr () )
  |> map (fun (((_, pats), _), body) -> 
    pats |> List.rev |> List.fold (fun body pat -> Typed.Typed((), Expr.Fun(pat, body))) body )) 

and prev () = delay (fun () ->
  ( token Token.Prev <*>
    term () )
  |> map (fun (_, body) ->
    Typed.Typed((), Expr.Prev(body)) ))

/// Parse a term (this handles most of the usual expressions)
and term () = delay (fun () ->
  func () <|>
  integer <|>
  var <|> 
  qvar <|>
  prev () <|>
  binding () <|>
  bracketed () )
