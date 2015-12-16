#r "packages/FunScript/lib/net40/FunScript.dll"
#r "packages/FunScript/lib/net40/FunScript.Interop.dll"
#r "packages/FunScript.TypeScript.Binding.lib/lib/net40/FunScript.TypeScript.Binding.lib.dll"
#r "packages/FunScript.TypeScript.Binding.jquery/lib/net40/FunScript.TypeScript.Binding.jquery.dll"
#load "parsec.fs"
#load "ast.fs"
#load "lexer.fs"
#load "parser.fs"
#load "solver.fs"
#load "typechecker.fs"
#load "pretty.fs"

open System.IO
open Coeffects
open Coeffects.Parser
open Coeffects.Parsec
open Coeffects.Ast
open Coeffects.TypeChecker
open Coeffects.Solver

let tests () =
  let source () = """
  let f = 
    let ?x = 1 in
    (fun a -> ?x + ?y) in
  let ?x = 2 in
  let ?y = 3 in f 0""".Trim()

  let source() = 
    "let f = (fun a -> ?x) in
    let ?x = 1 in (fun g -> g ?y) f"

  let source() =
    "fun a -> let ?x = 1 in (fun b -> ?x + ?y) a"

  let source() = 
    "let ?y = 1 in (fun a -> ?x + ?y + a)"

  let source() = 
    "let f = let ?y = 1 in (fun a -> ?x (a + ?y)) in f"

  let source() = 
    "?x + 1 + ?x 2"

  let source() = 
    """
let h = (fun x ->
  let f = (fun y -> prev y) in
  let g = (fun y -> prev x) in
  f (g 42)) in
h 0     """.Trim()


  let source () = "fun a -> ?x + ?y + a"
  let source () = "let (a, (b, (c), d)) = 1, (2,3,4) in a+b+c+d"
  let source () = "let a = 1,(2,3) in 5"

  let (Parsec.Parser lex) = Lexer.lexer
  let tokens = lex (List.ofArray (source().ToCharArray())) |> Option.get |> snd
  let tokens' = tokens |> List.filter (function Token.White _ -> false | _ -> true)
  let (Parsec.Parser pars) = Parser.expr ()
  let expr = pars tokens' |> Option.get |> snd
  let tt, ct = check (Context.empty CoeffectKind.PastValues) expr
  let solved, cequals = solve ct.TypeConstraints Map.empty []
  let csolved = ImplicitParams.solve (ct.CoeffectConstraints @ cequals)

  for c1, c2 in ct.CoeffectConstraints @ cequals do
    printfn "%A\n = %A\n" c1 c2 

  let typed = TypeChecker.typeCheck CoeffectKind.ImplicitParams expr
  let translated : Typed<unit> = translate (Typed((), Expr.Var "input")) [] typed


  TypeChecker.typeCheck CoeffectKind.ImplicitParams translated
  ()