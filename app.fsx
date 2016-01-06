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
fun y -> 
  let f = (fun x -> prev x) in 
  f y    """.Trim()


  let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 
   
  [<JSEmitInline("MathJax.Hub.Queue(['Typeset',MathJax.Hub,{0}]);")>]
  let typeSetElement (el:string) : unit = failwith "!"
  
  [<JSEmitInline("MathJax.Hub.Queue({0});")>]
  let queueAction(f:unit -> unit) : unit = failwith "!"


  type Value =
    | Unit
    | Integer of int
    | Function of (Value -> Value)
    | Tuple of Value list

    | ImplicitsComonad of Value * Microsoft.FSharp.Collections.Map<string, Value>
    | ListComonad of Value list

  type EvaluationContext = 
    { Variables : Microsoft.FSharp.Collections.Map<string, Value> 
      Kind : CoeffectKind }

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

  //let (|Fail|) s v = failwithf "%s %A" s v
  let (|Fail|) s _ = failwith s

  let evalImplicits ctx (Typed(_, expr)) = 
    match expr with
    | Expr.Builtin("merge", _) ->
        Value.Function(fun (Value.Tuple [Value.ImplicitsComonad(v1, d1); Value.ImplicitsComonad(v2, d2)] | Fail"Expected tuple of comonads" (v1,v2,d1,d2)) ->
          let m = d1 |> Map.toList |> List.fold (fun m (k, v) -> Map.add k v m) d2
          Value.ImplicitsComonad(Value.Tuple [v1; v2], m) ) |> Some

    | Expr.Builtin("duplicate", [_]) ->
        Value.Function(fun (Value.ImplicitsComonad(v, d) | Fail "Expected comonad with tuple" (v,d)) -> 
          Value.ImplicitsComonad(Value.Tuple [v; v], d) ) |> Some

    | Expr.Builtin("counit", _) ->
        Value.Function(fun (Value.ImplicitsComonad(v, _) | Fail "Expected comonad value" v) -> v ) |> Some

    | Expr.Builtin("cobind", [r; s]) ->
        Value.Function(fun (Value.Function(f) | Fail "Expected function" f) ->
          Value.Function(fun (Value.ImplicitsComonad(v, d) | Fail "Expected comonad" (v, d)) ->
            let r, s = Solver.ImplicitParams.evalCoeffect Map.empty r, Solver.ImplicitParams.evalCoeffect Map.empty s
            let a = f (Value.ImplicitsComonad(v, restrict d r))
            Value.ImplicitsComonad(a, restrict d s))) |> Some

    | Expr.Builtin("letimpl", [Coeffect.ImplicitParam(n, _); _; _]) ->
        Value.Function(fun (Value.Tuple [Value.ImplicitsComonad(c, d); v] | Fail "Expected tuple with implicit comonad" (c,d,v) ) ->
          Value.ImplicitsComonad(c, Map.add n v d) ) |> Some
   
    | Expr.Builtin("split", [r; s]) ->
        Value.Function(fun (Value.ImplicitsComonad(Value.Tuple [v1; v2], d) | Fail "Expected comonad of tuple" (v1,v2,d)) ->
          let r, s = Solver.ImplicitParams.evalCoeffect Map.empty r, Solver.ImplicitParams.evalCoeffect Map.empty s
          Value.Tuple [Value.ImplicitsComonad(v1, restrict d r); Value.ImplicitsComonad(v1, restrict d s)] ) |> Some

    | Expr.Builtin("lookup", [Coeffect.ImplicitParam(n, _)]) -> 
        Value.Function(fun (ImplicitsComonad(_, d) | Fail "Expected comonad value" d) -> d.[n]) |> Some

    | _ -> None

  let rec skip n l = 
    match n, l with
    | 0, l -> l
    | n, x::xs -> skip (n-1) xs
    | _ -> failwith "Not enough elements"

  let take n (l:'a list) = 
    let rec loop acc n (l:'a list) =
      match n, l with
      | 0, _ -> List.rev acc
      | n, x::xs -> loop (x::acc) (n-1) xs
      | _ -> failwith "Not enough elements"
    loop [] n l

  /// Workaround for a FunScript bug
  let unzip l = List.foldBack (fun (x,y) (xs,ys) -> x::xs, y::ys) l ([], [])

  let evalDataflow ctx (Typed(_, expr)) = 
    match expr with
    | Expr.Builtin("merge", _) ->
        Value.Function(fun (Value.Tuple [Value.ListComonad(vs1); Value.ListComonad(vs2)] | Fail"Expected tuple of comonads" (vs1,vs2)) ->
          Value.ListComonad(List.map2 (fun v1 v2 -> Value.Tuple [v1; v2]) vs1 vs2) ) |> Some

    | Expr.Builtin("duplicate", [_]) ->
        Value.Function(fun (Value.ListComonad(vs) | Fail "Expected comonad with tuple" (vs)) -> 
          Value.ListComonad(List.map (fun v -> Value.Tuple [v; v]) vs) ) |> Some

    | Expr.Builtin("counit", _) ->
        Value.Function(fun (Value.ListComonad [v] | Fail "Expected comonad value" v) -> v ) |> Some

    | Expr.Builtin("cobind", [r; s]) ->
        Value.Function(fun (Value.Function(f) | Fail "Expected function" f) ->
          Value.Function(fun (Value.ListComonad(vs) | Fail "Expected comonad" vs) ->
            let r, s = Solver.Dataflow.evalCoeffect Map.empty r, Solver.Dataflow.evalCoeffect Map.empty s
            Value.ListComonad
              [ for i in 0 .. s ->
                  vs |> skip i |> take (r+1) |> Value.ListComonad |> f ])) |> Some

    | Expr.Builtin("split", [r; s]) ->
        Value.Function(fun (Value.ListComonad(vs) | Fail "Expected comonad of tuple" vs) ->
          let a, b = vs |> List.map (fun (Value.Tuple[a;b] | Fail "Expected tuple" (a,b)) -> a, b) |> unzip
          let r, s = Solver.Dataflow.evalCoeffect Map.empty r, Solver.Dataflow.evalCoeffect Map.empty s
          Value.Tuple [Value.ListComonad(take (r+1) a); Value.ListComonad(take (s+1) b)] ) |> Some

    | Expr.Builtin("prev", _) ->
        Value.Function(fun (Value.ListComonad vs | Fail "Expected list comonad" (vs) ) ->
          Value.ListComonad(List.tail vs) ) |> Some
   
    | _ -> None

  let rec evalPrimitive ctx (Typed(_, expr)) =
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

    | Expr.Builtin(("fst" | "snd") as op, _) ->
        Value.Function(fun v ->
          match v with
          | Value.Tuple [v1; v2] -> if op = "fst" then v1 else v2
          | _ -> failwith "Expected two-element tuple")

    | Expr.Var(v) -> Map.find v ctx.Variables
    | Expr.Builtin("input", _) -> Map.find "input" ctx.Variables
    | Expr.Integer n -> Value.Integer n
    //| e -> failwithf "%A" e
    | _ -> failwith "Eval failed"

  and eval ctx expr =
    let special = 
      match ctx.Kind with
      | CoeffectKind.ImplicitParams -> evalImplicits ctx expr 
      | CoeffectKind.PastValues -> evalDataflow ctx expr 
      | _ -> failwith "Can only eval imploicits or past values"
    match special with
    | None -> evalPrimitive ctx expr
    | Some v -> v

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
      //path "/" >>= Files.file (Path.Combine(__SOURCE_DIRECTORY__, "web", "index.html"))
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