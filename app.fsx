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
#load "solver.fs"
#load "typechecker.fs"

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

  let appendTitleCls title cls body (sb:string[]) =
    if title = "" then appendCls cls body sb else
    sb.push("<span title='")
    sb.push(title)
    sb.push("' class='")
    sb.push(cls)
    sb.push("'>")
    sb.push(body)
    sb.push("</span>")

  let printPat title sb pat = 
    match pat with
    | Pattern.Var(s) -> appendTitleCls title "i" s sb
    | Pattern.QVar(s) -> appendTitleCls title "i" ("?" + s) sb

  let rec formatCoeff coeff =
    match coeff with
    | Coeffect.Variable s -> s
    | Coeffect.ImplicitParam(n, t) -> "?" + n + ":" + (formatTyp t)
    | Coeffect.Merge(c1, c2) -> formatCoeff c1 + " ^ " + formatCoeff c2
    | Coeffect.Split(c1, c2) -> formatCoeff c1 + " + " + formatCoeff c2
    | Coeffect.Seq(c1, c2) -> formatCoeff c1 + " * " + formatCoeff c2
    | Coeffect.Ignore -> "ign"
    | Coeffect.Use -> "use"

  and formatTyp typ = 
    match typ with 
    | Type.Variable s -> "&quot;" + s
    | Type.Func(c, t1, t2) -> "(" + formatTyp t1 + " -{ " + formatCoeff c + " }&gt; " + formatTyp t2 + ")"
    | Type.Primitive s -> s

  let rec printExpr sb (Typed.Typed((coeff, typ), expr)) =
    match expr with
    | Expr.Var(s) -> appendTitleCls (formatTyp typ) "i" s sb
    | Expr.QVar(s) -> appendCls "i" ("?" + s) sb
    | Expr.Integer(n) -> appendCls "n" (string n) sb
    | Expr.Fun(pat, body) -> 
        append "(" sb
        appendCls "k" "fun" sb    
        append " " sb
        printPat "" sb pat
        append " " sb
        appendCls "k" "->" sb
        append " " sb
        printExpr sb body
        append ")" sb
    | Expr.Let(pat, (Typed.Typed((coeff, vtyp), _) as expr), body) -> 
        appendCls "k" "let" sb
        append " " sb
        printPat (formatTyp vtyp) sb pat
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
        printExpr sb e2
    
  
  module Tex = 
    let inl s (arr:string[]) = 
      arr.push(s); arr
    let kvd s (arr:string[]) = 
      arr |> inl ("{\\color{kvd}\\text{" + s + "}}")
    let num n (arr:string[]) = 
      arr |> inl ("{\\color{num} " + string n + "}")
    let pattern pat strs = 
      match pat with 
      | Pattern.Var v -> strs |> inl v
      | Pattern.QVar v -> strs |> inl ("?" + v)

    let limit n f g (arr:string[]) =
      let l1 = arr.Length
      let _ = f arr
      if arr.Length <= l1 + n then arr
      else 
        let _ = arr.splice(float l1, float (arr.Length - l1)) 
        g arr

    let rec expr (Typed.Typed((c, t),e)) (ar:string[]) = 
      match e with
      | Expr.Var(v) -> ar |> inl v
      | Expr.QVar(v) -> ar |> inl ("?" + v)
      | Expr.Integer(n) -> ar |> num n
      | Expr.App(e1, e2) ->
          ar |> expr e1 |> inl "~" |> expr e2
      | Expr.Let(pat, arg, body) ->
          ar |> kvd "let" |> inl "~" |> pattern pat |> inl "~=~" 
             |> limit 8 (expr arg) (inl "(\\ldots)") |> inl "~" |> kvd "in" |> inl "~" 
             |> limit 8 (expr body) (inl "(\\ldots)")
      | _ -> 
          ar |> inl "???"

    let rec flattenCoeffects c = 
      match c with
      | Coeffect.Ignore | Coeffect.Use -> []
      | Coeffect.ImplicitParam(s, _) -> ["?" + s]
      | Coeffect.Merge(c1, c2) | Coeffect.Split(c1, c2) | Coeffect.Seq(c1, c2) -> 
          flattenCoeffects c1 @ flattenCoeffects c2
      | Coeffect.Variable _ -> failwith "Unresolved coeffect variable"

    let coeff c (ar:string[]) =
      ar |> inl (String.concat "," (flattenCoeffects c))

    let rec typ t (ar:string[]) =
      match t with 
      | Type.Func(c, t1, t2) -> ar |> typ t1 |> inl "\\xrightarrow{" |> coeff c |> inl "}" |> typ t2
      | Type.Primitive(s) -> ar |> inl ("\\text{" + s + "}")
      | Type.Variable(s) -> ar |> inl ("`" + s)
          

    let typed (Typed.Typed((c, t), e) as te) (ar:string[]) =
      ar |> inl "\\,{\\small @}\\," |> coeff c |> inl "\\vdash " |> expr te |> inl ":" |> typ t

    let judgement (Typed.Typed((c, t), e) as te) (ar:string[]) = 
      match e with
      | Expr.Let(pat, arg, body) ->
          ar |> inl "\\dfrac{" |> typed arg |> inl "\\quad " |> typed body |> inl "}{" |> typed te |> inl "}"


(*  let source3 = "1+2+3+4^2^2*5"
  let source = source2
  let (Parsers.Parser p) = Lexer.lexer
  let tokens = p (List.ofSeq source) |> Option.get |> snd
  let (Parsers.Parser p2) = expr ()
  p2 tokens
  |> Option.get |> snd
*)
  let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 
   
  [<JSEmitInline("MathJax.Hub.Queue(['Typeset',MathJax.Hub,{0}]);")>]
  let typeSetElement (el:string) : unit = failwith "!"

  let main () =
    let btn = Globals.document.getElementById("btn") :?> HTMLButtonElement
    let input = Globals.document.getElementById("input") :?> HTMLTextAreaElement
    let output = Globals.document.getElementById("output") :?> HTMLPreElement
    let judgement = Globals.document.getElementById("judgement") :?> HTMLPreElement
    input.value <- source()
    btn.addEventListener_click(fun e ->
      let (Parsec.Parser lex) = Lexer.lexer
      let tokens = lex (List.ofArray (input.value.ToCharArray())) |> Option.get |> snd
      let tokens = tokens |> filter (function Token.White _ -> false | _ -> true)
      let (Parsec.Parser pars) = Parser.expr ()
      let expr = pars tokens |> Option.get |> snd
      let arr : string[] = [| |]
      let typed = TypeChecker.typeCheck expr
      printExpr arr typed
      // Globals.alert(arr.join(""))
      output.innerHTML <- arr.join("")

      // $('.mtable').on("mouseenter", function() { $(this).css({backgroundColor: '#c0ffc0'}) }).on("mouseleave", function() { $(this).css({backgroundColor: '#ffffff'}) });

      let arr2 : string[] = [| |]
      let arr2' = Tex.judgement typed arr2
      judgement.innerHTML <- "\\[" + arr2.join("") + "\\]"
      Globals.alert( arr2.join("") )
      typeSetElement "judgement"

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