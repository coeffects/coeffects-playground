#r "packages/Suave/lib/net40/Suave.dll"
#r "packages/FunScript/lib/net40/FunScript.dll"
#r "packages/FunScript/lib/net40/FunScript.Interop.dll"
#r "packages/FunScript.TypeScript.Binding.lib/lib/net40/FunScript.TypeScript.Binding.lib.dll"
open System.IO
open FunScript
open FunScript.Compiler

open Suave
open Suave.Web
open Suave.Http
open Suave.Types
open Suave.Http.Applicatives

#load "parsec.fs"
#load "ast.fs"
#load "lexer.fs"
#load "parser.fs"

// ------------------------------------------------------------------------------------------------
// Translating F# code to JavaScript using FunScript
// ------------------------------------------------------------------------------------------------

[<JSEmitInline("{0}.join('')")>]
let newString(c:char[]) : string = failwith "!"

let replacer = 
  ExpressionReplacer.createUnsafe 
    <@ fun (c:char[]) -> new System.String(c) @> <@ fun c -> newString c @>

let translate q = Compiler.Compile(q, fun l -> replacer :: l)

// ------------------------------------------------------------------------------------------------
//
// ------------------------------------------------------------------------------------------------

open Coeffects
open Coeffects.Ast
open FunScript.TypeScript
open System.Text

[<ReflectedDefinition>]
module Client = 
  let source () = """
let f = 
  let ?x = 1 in
  (fun a -> ?x + ?y) in
let ?x = 2 in
let ?y = 3 in f 0""".Trim()

  type 'T``[]`` with
    [<JSEmitInline("{0}.push({1})")>]
    member x.push(v:'T) : unit = failwith "!"

  let append body (sb:string[]) = 
    sb.push(body)

  let appendCls cls body (sb:string[]) = 
    sb.push("<span class='")
    sb.push(cls)
    sb.push("'>")
    sb.push(body)
    sb.push("</span>")

  let printPat sb pat = 
    match pat with
    | Pattern.Var(s) -> appendCls "i" s sb
    | Pattern.QVar(s) -> appendCls "i" ("?" + s) sb

  let rec printExpr sb expr =
    match expr with
    | Expr.Var(s) -> appendCls "i" s sb
    | Expr.QVar(s) -> appendCls "i" ("?" + s) sb
    | Expr.Integer(n) -> appendCls "n" (string n) sb
    | Expr.Fun(pats, body) -> 
        append "(" sb
        appendCls "k" "fun" sb    
        for pat in pats do
          append " " sb
          printPat sb pat
        append " " sb
        appendCls "k" "->" sb
        append " " sb
        printExpr sb body
        append ")" sb
    | Expr.Let(pat, expr, body) -> 
        appendCls "k" "let" sb
        append " " sb
        printPat sb pat
        append " " sb
        appendCls "op" "=" sb
        append " " sb
        printExpr sb expr
        append " " sb
        appendCls "k" "in" sb
        append "\n" sb
        printExpr sb body
    | Expr.App(e1, e2) ->
        printExpr sb e1
        append " " sb
        printExpr sb e2
    | Expr.Binary(op, e1, e2) -> 
        printExpr sb e1
        append " " sb
        appendCls "op" op sb
        append " " sb
        printExpr sb e1
    


(*  let source3 = "1+2+3+4^2^2*5"
  let source = source2
  let (Parsers.Parser p) = Lexer.lexer
  let tokens = p (List.ofSeq source) |> Option.get |> snd
  let (Parsers.Parser p2) = expr ()
  p2 tokens
  |> Option.get |> snd
*)
  let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 
   
  let main () =
    let btn = Globals.document.getElementById("btn") :?> HTMLButtonElement
    let input = Globals.document.getElementById("input") :?> HTMLTextAreaElement
    let output = Globals.document.getElementById("output") :?> HTMLPreElement
    input.value <- source()
    btn.addEventListener_click(fun e ->
      let (Parsec.Parser lex) = Lexer.lexer
      let tokens = lex (List.ofArray (input.value.ToCharArray())) |> Option.get |> snd
      let tokens = tokens |> filter (function Token.White _ -> false | _ -> true)
      let (Parsec.Parser pars) = Parser.expr ()
      let expr = pars tokens |> Option.get |> snd
      let arr : string[] = [| |]
      printExpr arr expr
      Globals.alert(arr.join(""))
      output.innerHTML <- arr.join("")
      null
    )


let script = 
  translate <@ Client.main() @>
  |> sprintf "$(function() { %s })"

let app = 
  choose 
    [ path "/" >>= request (fun _ -> 
        Successful.OK(File.ReadAllText(__SOURCE_DIRECTORY__ + "/web/index.html"))) 
      path "/script.js" >>= Successful.OK script ]

// -------------------------------------------------------------------------------------------------
// To run the web site, you can use `build.sh` or `build.cmd` script, which is nice because it
// automatically reloads the script when it changes. But for debugging, you can also use run or
// run with debugger in VS or XS. This runs the code below.
// -------------------------------------------------------------------------------------------------
#if INTERACTIVE
#else
open Suave.Web
let cfg =
  { defaultConfig with
      bindings = [ HttpBinding.mk' HTTP  "127.0.0.1" 8011 ]
      homeFolder = Some __SOURCE_DIRECTORY__ }
let _, server = startWebServerAsync cfg app
Async.Start(server)
System.Diagnostics.Process.Start("http://localhost:8011")
System.Console.ReadLine() |> ignore
#endif