#load "packages/FSharp.Formatting/FSharp.Formatting.fsx"
#r "packages/Suave/lib/net40/Suave.dll"
#r "packages/FunScript/lib/net40/FunScript.dll"
#r "packages/FunScript/lib/net40/FunScript.Interop.dll"
#r "packages/FunScript.TypeScript.Binding.lib/lib/net40/FunScript.TypeScript.Binding.lib.dll"
#r "packages/FunScript.TypeScript.Binding.jquery/lib/net40/FunScript.TypeScript.Binding.jquery.dll"
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
#load "pretty.fs"
#load "translation.fs"
#load "evaluation.fs"

// ------------------------------------------------------------------------------------------------
// Translating F# code to JavaScript using FunScript
// ------------------------------------------------------------------------------------------------

open FunScript.TypeScript

[<JSEmitInline("{0}.join('')")>]
let newString(c:char[]) : string = failwith "!"

[<JSEmitInline("$(this)")>]
let jthis() : JQuery = failwith "!"

[<JSEmitInline("$({0})")>]
let jq s : JQuery = failwith "!"

let replacer = 
  ExpressionReplacer.createUnsafe 
    <@ fun (c:char[]) -> new System.String(c) @> <@ fun c -> newString c @>

let translate q = Compiler.Compile(q, fun l -> replacer :: l)

// ------------------------------------------------------------------------------------------------
//
// ------------------------------------------------------------------------------------------------

open Coeffects
open Coeffects.Ast
open Coeffects.Pretty
open Coeffects.Evaluation
open System.Text

[<ReflectedDefinition>]
module Client = 
  let source prefix = 
    if prefix = "impl1" then 
      """
let f = 
  let ?x = 1 in
  (fun a -> ?x + ?y) in
let ?x = 2 in
let ?z = 3 in f 0""".Trim()
    else 
      """
fun y -> 
  let f = (fun x -> prev x) in 
  f y    """.Trim()


  let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 
   
  [<JSEmitInline("MathJax.Hub.Queue(['Typeset',MathJax.Hub,{0}]);")>]
  let typeSetElement (el:string) : unit = failwith "!"
  
  [<JSEmitInline("MathJax.Hub.Queue({0});")>]
  let queueAction(f:unit -> unit) : unit = failwith "!"

  let setup kind prefix = 
    let btn = Globals.document.getElementById(prefix + "-btn") :?> HTMLButtonElement
    let input = Globals.document.getElementById(prefix + "-input") :?> HTMLTextAreaElement
    let output = Globals.document.getElementById(prefix + "-output") :?> HTMLPreElement
    let transl = Globals.document.getElementById(prefix + "-transl") :?> HTMLPreElement
    let judgement = Globals.document.getElementById(prefix + "-judgement") :?> HTMLPreElement
    let judgementTemp = Globals.document.getElementById(prefix + "-judgement-temp") :?> HTMLPreElement

    let playground = Globals.document.getElementById(prefix + "-playground") :?> HTMLPreElement

    input.value <- source prefix
    btn.addEventListener_click(fun e ->
      let (Parsec.Parser lex) = Lexer.lexer
      let source = input.value

      // TODO: Rename all type/coeffect variables before translation to remove clashes
      
      let tokens = lex (List.ofArray (source.ToCharArray())) |> Option.get |> snd
      let tokens = tokens |> filter (function Token.White _ -> false | _ -> true)
      let (Parsec.Parser pars) = Parser.expr ()
      let expr = pars tokens |> Option.get |> snd
      let typed = TypeChecker.typeCheck (fun _ _ -> failwith "!") kind expr
      output.innerHTML <- Html.print (Html.printExpr kind prefix 0 [] typed)
      
      let transle  = 
        Translation.translate (Typed((), Expr.Builtin("input", []))) [] typed 
        |> Translation.contract
        |> TypeChecker.typeCheck (Translation.builtins (TypeChecker.coeff typed)) (CoeffectKind.Embedded kind)

      transl.innerHTML <- Html.print (Html.printExpr kind prefix 0 [] transle)

      let el s (attrs:list<string*string>) children = 
        let jp = attrs |> List.fold (fun (j:JQuery) (k, v) -> j.attr(k, v)) (jq("<" + s + " />"))
        children |> List.fold (fun (p:JQuery) (c:JQuery) -> p.append(c)) jp
      let css (attrs:list<string*string>) (j:JQuery) = 
        attrs |> List.fold (fun (j:JQuery) (k, v) -> j.css(k, v)) j
      let html (s:string) (j:JQuery) = j.html(s)
      let appendTo (p:JQuery) (j:JQuery) = j.appendTo(p)
      let click (f:unit -> unit) (j:JQuery) = j.click(fun _ -> f(); obj())

      playground.innerHTML <- "";
      match kind, typed with
      | CoeffectKind.PastValues, Typed((_, Coeffect.Past m, Type.Func(Coeffect.Past n, _, _)), _) ->
          let pl = jq(playground)
          let pastValues = [ for i in 0 .. n -> i, el "input" [("type","text"); ("class","form-control")] [] |> css ["width","50px"] ]
          el "form" [("class","form-inline")] [
            el "div" [("class","input-group")] [
              yield el "div" [("class","input-group-addon")] [] |> html "input = ["
              for i, pv in pastValues do
                if i <> 0 then 
                  yield el "div" [("class","input-group-addon")] [] |> css ["padding","6px 8px 6px 4px"] |> html ";"
                yield pv 
              yield el "div" [("class","input-group-addon")] [] |> html "]" ]
          ] |> appendTo pl |> ignore
          el "button" [ ("class", "btn btn-success") ] [] 
          |> html "Run"
          |> click (fun () ->
            let input = Value.ListComonad [ for _ in 0 .. m -> Value.Unit ]
            let arg = Value.ListComonad [ for _, i in pastValues -> Value.Integer(1 * unbox(i._val())) ]
            let res = 
              let (Value.Function f | Fail "Expected function!" f) = eval { Kind = kind; Variables = Map.ofSeq ["input", input] } transle
              f arg
            match res with 
            | Value.Integer n -> Globals.window.alert(string n)
            | _ -> Globals.window.alert("Something weird") )
          |> appendTo pl |> ignore

      | CoeffectKind.ImplicitParams, Typed((_, c, _), _) ->
          let coeffs = Solver.ImplicitParams.evalCoeffect Map.empty c |> Set.toList
          let pl = jq(playground)
          let fg = el "div" [ ("class","form-group") ] [] |> appendTo pl
          let inputs = 
            [ for c in coeffs -> 
                let input = el "input" [ ("type","text"); ("class","form-control") ] []
                let div = el "div" [ ("class","input-group-addon") ] [] |> css [ ("min-width", "70px") ] |> html ("?" + c + " = ")
                el "div" [ ("class","input-group") ] [ div; input ] |> css [ ("margin-bottom", "10px") ] |> appendTo fg |> ignore
                c, input ]

          el "div" [("class","form-group")] [
            el "button" [ ("class", "btn btn-success") ] [] 
            |> html "Run"
            |> click (fun () ->
              let input = Value.ImplicitsComonad(Value.Unit, Map.ofList [ for c, i in inputs -> c, Value.Integer(1 * unbox(i._val())) ])
              let res = eval { Kind = kind; Variables = Map.ofSeq ["input", input] } transle
              match res with 
              | Value.Integer n -> Globals.window.alert(string n)
              | _ -> Globals.window.alert("Something weird")
            )
          ] |> appendTo pl |> ignore
      | _ -> ()

      let rec findSubExpression locations (Typed.Typed(_, e) as te) : Typed<Vars * Coeffect * Type> = 
        match locations, e with
        | [], _ -> te
        | 0::t, (Expr.Let(_, e, _) | Expr.App(e, _) | Expr.Binary(_, e, _) | Expr.Fun(_, e) | Expr.Prev(e) )
        | 1::t, (Expr.Let(_, _, e) | Expr.App(_, e) | Expr.Binary(_, _, e)) ->
           findSubExpression t e
        | _ -> failwith "Invalid path"

      let locations : ref<int list> = ref []

      let rec typeset () =
        let e = findSubExpression (List.rev locations.Value) typed
        let arr2 : string[] = [| |]
        let root = locations.Value |> List.isEmpty
        let arr2' = MathJax.derivation kind root e arr2
        judgementTemp.innerHTML <- "\\[" + arr2.join("") + "\\]"
        typeSetElement (prefix + "-judgement-temp")

        let getNewPath (jo:JQuery) =
          let index = jq("#" + prefix + " .mtable").index(jo)
          let length = jq("#" + prefix + " .mtable").length
          let current = if root then length - 1.0 else length - 2.0
          if index = current then
            true, locations.Value
          elif index > current then
            false, locations.Value |> List.tail
          else 
            false, (int index) :: locations.Value

        let highlight (jo:JQuery) (thisClr:string) (currClr:string) = 
          let current, path = getNewPath jo
          let path = List.rev path
          let id = prefix + "-p-" + (String.concat "-" (List.map string path))
          let clr = if current then currClr else thisClr
          jq("#" + id).css("backgroundColor", clr) |> ignore
          jo.css("backgroundColor", clr) |> ignore
  
        queueAction(fun () ->
          judgement.innerHTML <- judgementTemp.innerHTML
          judgementTemp.innerHTML <- ""
          
          jq("#" + prefix + " .mtable").css("cursor", "pointer") |> ignore
          let currIndex = jq("#" + prefix + " .mtable").length - (if root then 1.0 else 2.0)
          jq("#" + prefix + " .mtable").eq(currIndex).css("cursor","default") |> ignore

          jq("#" + prefix + " .mtable")
            .on("click", fun e o ->
              jq("#" + prefix + " .p-span").css("backgroundColor", "transparent") |> ignore
              locations.Value <- snd (getNewPath (jthis()))
              typeset ()
              box () )
            .on("mouseenter", fun e o ->
              highlight (jthis()) "#c0ffc0" "#ffffc0"
              box () )
            .on("mouseleave", fun e o ->
              highlight (jthis()) "transparent" "transparent"
              box () )
          |> ignore )

      typeset ()

      null
    )

  let main () =
    setup CoeffectKind.ImplicitParams "impl1"
    setup CoeffectKind.PastValues "df1"

let script = 
  translate <@ Client.main() @>
  |> sprintf "$(function() { %s })"

let app = 
  choose 
    [ path "/" >>= request (fun r ->
        let fi = File.ReadAllText(Path.Combine(__SOURCE_DIRECTORY__, "web", "index.html"))
        let reg = RegularExpressions.Regex(">>>>(.*?)<<<<", RegularExpressions.RegexOptions.Singleline)
        let counter = ref 0
        let f = reg.Replace(fi,RegularExpressions.MatchEvaluator(fun m -> 
          let md = m.Groups.[1].Value.Split [|'\n'|]
          let drop = md |> Seq.filter (System.String.IsNullOrWhiteSpace >> not) |> Seq.map (Seq.takeWhile ((=) ' ') >> Seq.length) |> Seq.min
          let md = md |> Seq.map (fun s -> if System.String.IsNullOrWhiteSpace s then s else s.Substring(drop)) |> String.concat "\n"
          let doc = FSharp.Literate.Literate.ParseMarkdownString(md)
          //let doc = FSharp.Literate.Literate.FormatLiterateNodes(doc)
          incr counter
          FSharp.Literate.Literate.WriteHtml(doc, prefix=sprintf "s%d" counter.Value, lineNumbers=false) 
          ))
        Successful.OK f      
      )
      path "/test" >>= Files.file (Path.Combine(__SOURCE_DIRECTORY__, "web", "test.html"))
      Files.browse (Path.Combine(__SOURCE_DIRECTORY__, "web"))
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