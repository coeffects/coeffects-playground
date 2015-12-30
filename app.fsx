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
let h = prev (fun y -> 
  (fun x -> 1 + prev x) (prev y))
in h 42  """.Trim()


  let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 
   
  [<JSEmitInline("MathJax.Hub.Queue(['Typeset',MathJax.Hub,{0}]);")>]
  let typeSetElement (el:string) : unit = failwith "!"
  
  [<JSEmitInline("MathJax.Hub.Queue({0});")>]
  let queueAction(f:unit -> unit) : unit = failwith "!"


  type Value =
    | Unit
    | Integer of int
    | ImplicitsComonad of Value * Microsoft.FSharp.Collections.Map<string, Value>
    | Function of (Value -> Value)
    | Tuple of Value list

  type EvaluationContext = 
    { Variables : Microsoft.FSharp.Collections.Map<string, Value> }

  let rec bind value (TypedPat(_, pattern)) vars = 
    match pattern, value with
    | Pattern.Var n, v -> Map.add n v vars
    | Pattern.Tuple pats, Value.Tuple vals when pats.Length = vals.Length ->
        List.zip pats vals |> List.fold (fun ctx (p, v) -> bind v p ctx) vars
    | _ -> failwith "Pattern does not match value"        

  let operators = 
    Map.ofList [ "+", (+); "-", (-); "*", (*); "/", (/); "^", pown ] 

  let restrict (m:Microsoft.FSharp.Collections.Map<string, Value>) s = 
    Map.ofList [ for v in Set.toList s -> v, Map.find v m ]

  let (|Fail|) s _ = failwith s

  let rec eval ctx (Typed(_, expr)) =
    match expr with

    | Expr.Binary(op, l, r) ->
        let op = match operators.TryFind op with Some(o) -> o | _ -> failwith "Unexpected operator"
        match eval ctx l, eval ctx r with
        | Value.Integer l, Value.Integer r -> Value.Integer(op l r)
        | _ -> failwith "Expected two numbers"

    | Expr.Tuple(args) ->
        Value.Tuple(List.map (eval ctx) args)
    | Expr.Let(pat, arg, body) ->
        eval { ctx with Variables = bind (eval ctx arg) pat ctx.Variables } body

    | Expr.App(e1, e2) ->
        match eval ctx e1, eval ctx e2 with
        | Value.Function f, v -> f v
        | _ -> failwith "Expected function"

    | Expr.Fun(pat, body) ->
        Value.Function(fun v ->
          eval { ctx with Variables = bind v pat ctx.Variables } body)

    | Expr.Builtin("merge", _) ->
        Value.Function(fun v ->
          match v with
          | Value.Tuple [Value.ImplicitsComonad(v1, d1); Value.ImplicitsComonad(v2, d2)] ->
              let m = d1 |> Map.toList |> List.fold (fun m (k, v) -> Map.add k v m) d2
              Value.ImplicitsComonad(Value.Tuple [v1; v2], m)
          | _ -> failwith "Expected tuple of comonad values")

    | Expr.Builtin("duplicate", [_]) ->
        Value.Function(fun v ->
          match v with 
          | Value.ImplicitsComonad(v, d) -> Value.ImplicitsComonad(Value.Tuple [v; v], d)
          | _ -> failwith "Expected dictionary with tuple value")

    | Expr.Builtin("counit", _) ->
        Value.Function(fun v ->
          match v with
          | Value.ImplicitsComonad(v, _) -> v 
          | _ -> failwith "Expected comonad value")

    | Expr.Builtin(("fst" | "snd") as op, _) ->
        Value.Function(fun v ->
          match v with
          | Value.Tuple [v1; v2] -> if op = "fst" then v1 else v2
          | _ -> failwith "Expected two-element tuple")

    | Expr.Builtin("cobind", [r; s]) ->
        Value.Function(fun (Value.Function(f) | Fail "Expected function" f) ->
          Value.Function(fun (Value.ImplicitsComonad(v, d) | Fail "Expected comonad" (v, d)) ->
            let r, s = Solver.ImplicitParams.evalCoeffect Map.empty r, Solver.ImplicitParams.evalCoeffect Map.empty s
            let a = f (Value.ImplicitsComonad(v, restrict d r))
            Value.ImplicitsComonad(a, restrict d s)))

    | Expr.Builtin("letimpl", [Coeffect.ImplicitParam(n, _); _; _]) ->
        Value.Function(fun (Value.Tuple [Value.ImplicitsComonad(c, d); v] | Fail "Expected tuple with implicit comonad" (c,d,v) ) ->
          Value.ImplicitsComonad(c, Map.add n v d) )
   
    | Expr.Builtin("split", [r; s]) ->
        Value.Function(fun v ->
          match v with 
          | Value.ImplicitsComonad(Value.Tuple [v1; v2], d) ->
              let r, s = Solver.ImplicitParams.evalCoeffect Map.empty r, Solver.ImplicitParams.evalCoeffect Map.empty s
              Value.Tuple [Value.ImplicitsComonad(v1, restrict d r); Value.ImplicitsComonad(v1, restrict d s)]
          | _ -> failwith "Expected dictionary with tuple value")

    | Expr.Builtin("lookup", [Coeffect.ImplicitParam(n, _)]) -> 
        Value.Function(fun v -> 
          match v with
          | ImplicitsComonad(_, d) -> d.[n]
          | _ -> failwith "Expected dictionary")

    | Expr.Var(v) -> Map.find v ctx.Variables
    | Expr.Builtin("input", _) -> Map.find "input" ctx.Variables
    | Expr.Integer n -> Value.Integer n
    //| e -> failwithf "%A" e
    | _ -> failwith "Eval failed"

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

      (*
      let source = "(fun x -> ?y)"
      
      // TODO: Rename all type/coeffect variables before translation to remove clashes
      // TODO: Separate solver for translated terms (ignores all coeffects from
      // expressions; only unifies coeffect variables from comonad types - cequals)
       
      let kind = CoeffectKind.ImplicitParams
      *)

      let tokens = lex (List.ofArray (source.ToCharArray())) |> Option.get |> snd
      let tokens = tokens |> filter (function Token.White _ -> false | _ -> true)
      let (Parsec.Parser pars) = Parser.expr ()
      let expr = pars tokens |> Option.get |> snd
      let typed = TypeChecker.typeCheck (fun _ _ -> failwith "!") kind expr
      output.innerHTML <- Html.print (Html.printExpr kind prefix 0 [] typed)
      
//(*
      let transle  = 
        Translation.translate (Typed((), Expr.Builtin("input", []))) [] typed 
        |> Translation.contract
        |> TypeChecker.typeCheck (Translation.builtins (TypeChecker.coeff typed)) (CoeffectKind.Embedded kind)

      transl.innerHTML <- Html.print (Html.printExpr kind prefix 0 [] transle)
//*)

      match kind, typed with
      | CoeffectKind.ImplicitParams, Typed((_, c, _), _) ->
          let pl = jq(playground)
          let coeffs = Solver.ImplicitParams.evalCoeffect Map.empty c |> Set.toList
          let inputs = 
            [ for c in coeffs ->
                let input = jq("<input />")
                pl.append(jq("<p>?" + c + "</p>").append(input)) |> ignore
                c, input ]

          jq("<button>Run</button>").click(fun c -> 
            //let input = Value.ImplicitsComonad(Value.Unit, Map.ofList [ "y", Value.Integer(1) ])
            let input = Value.ImplicitsComonad(Value.Unit, Map.ofList [ for c, i in inputs -> c, Value.Integer(1 * unbox(i._val())) ])
            let res = eval { Variables = Map.ofSeq ["input", input] } transle
            match res with 
            | Value.Integer n -> Globals.window.alert(string n)
            | _ -> Globals.window.alert("Something weird")
            obj()).appendTo(pl)
          |> ignore
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