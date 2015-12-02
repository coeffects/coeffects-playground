// ------------------------------------------------------------------------------------------------
// Lexer for a mini-ML langauge - turns list<char> into list<Token>
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Lexer

open Coeffects.Parsec
open Coeffects.Ast

// Lookup tables for supported keywords and operators
let keywords = Map.ofSeq [ "fun", Token.Fun; "let", Token.Let; "in", Token.In ]
let operators = set [ '+'; '-'; '*'; '/'; '^' ]

// Parsing basic things like letters and numbers
let char c token = prefix [c] token
let string (s:string) token = prefix (List.ofArray(s.ToCharArray())) token

let letter = pred (fun c -> (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))
let number = pred (fun c -> (c >= '0' && c <= '9'))

let integer = oneOrMore number |> map (fun digits ->
  Token.Integer(int (System.String(Array.ofList digits))) )

let operator = pred operators.Contains |> map (fun op ->
  Token.Operator(op.ToString()) )

/// Parse letter followed by zero or more letters and/or numbers
let keywordOrIdent = 
  letter <*> (zeroOrMore (letter <|> number))
  |> map (fun (c, cs) -> 
      let s = System.String(Array.ofList (c::cs))
      match keywords.TryFind s with
      | Some token -> token
      | _ -> Token.Ident(s) )

/// Parse identifier prefixed with question mark (implicit parameter)
let questionIdent = 
  (pred ((=) '?')) <*> letter <*> (zeroOrMore (letter <|> number))
  |> map (fun ((_, c), cs) ->
      Token.QIdent(System.String(Array.ofList (c::cs))) )

/// We parse and keep whitespace, but filter it out later 
let whitespace =
  oneOrMore (pred (fun c -> c = ' ' || c = '\n'))
  |> map (fun whites -> Token.White(System.String(Array.ofList whites)))

/// The main lexer for our mini-ML language
let lexer = 
  sequenceChoices 
    [ char '(' Token.LParen
      char ')' Token.RParen 
      char '=' Token.Equals
      string "->" Token.Arrow
      integer
      operator
      questionIdent
      keywordOrIdent
      whitespace ] 