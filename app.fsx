#if INTERACTIVE
#load "packages/FSharp.Formatting/FSharp.Formatting.fsx"
#endif
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
#load "errors.fs"
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

// ------------------------------------------------------------------------------------------------
// Create a UI where the user can enter inputs and run the translated program
// ------------------------------------------------------------------------------------------------

  let el s (attrs:list<string*string>) children = 
    let jp = attrs |> List.fold (fun (j:JQuery) (k, v) -> j.attr(k, v)) (jq("<" + s + " />"))
    children |> List.fold (fun (p:JQuery) (c:JQuery) -> p.append(c)) jp
  let css (attrs:list<string*string>) (j:JQuery) = 
    attrs |> List.fold (fun (j:JQuery) (k, v) -> j.css(k, v)) j
  let html (s:string) (j:JQuery) = j.html(s)
  let appendTo (p:JQuery) (j:JQuery) = j.appendTo(p)
  let click (f:unit -> unit) (j:JQuery) = j.click(fun _ -> f(); obj())
  let cls (s:string) (j:JQuery) = j.addClass(s)

  let setupPlayground prefix kind tyinfo transle = 
    let playground = Globals.document.getElementById(prefix + "-playground") :?> HTMLPreElement
    playground.innerHTML <- "";
    match kind, tyinfo with
    | CoeffectKind.PastValues, (_, Coeffect.Past m, Type.Func((Coeffect.Past n, _), _, _)) ->
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
          let arg = Value.ListComonad [ for _, i in pastValues -> Value.Number(1.0 * unbox(i._val())) ]
          let res = 
            let (Value.Function f | Fail "Expected function!" f) = eval { Kind = kind; Variables = Map.ofSeq ["input", input] } transle // Flat input!
            f arg
          match res with 
          | Value.Number n -> Globals.window.alert(string n)
          | _ -> Globals.window.alert("Something weird") )
        |> appendTo pl |> ignore

    | CoeffectKind.ImplicitParams, (_, c, _) ->
        let coeffs = Solver.ImplicitParams.evalCoeffect Map.empty c |> Set.toList
        let pl = jq(playground)
        let fg = el "table" [] [] |> appendTo pl
        let inputs = 
          [ for c in coeffs -> 
              let input = el "input" [ ("type","text"); ("placeholder", "0"); ("class","form-control") ] []
              let label = el "td" [] [] |> html ("<code>?" + c + "</code> =") |> cls "label"
              el "tr" [] [ label; el "td" [] [input] ] |> appendTo fg |> ignore
              c, input ]

        let result =
          let input = el "input" [ ("type","text"); ("disabled", "disabled"); ("placeholder", "0"); ("class","form-control") ] []
          let label = el "td" [] [] |> html ("<code>result</code> =") |> cls "label"
          el "tr" [] [ label; el "td" [] [input] ] |> cls "result" |> appendTo fg |> ignore
          input
              
        let evaluate () = 
          let input = Value.ImplicitsComonad(Value.Unit, Map.ofList [ for c, i in inputs -> c, Value.Number(1.0 * unbox(i._val())) ])
          let res = eval { Kind = kind; Variables = Map.ofSeq ["input", input] } transle // Flat input
          match res with 
          | Value.Number n -> result._val(string n) |> ignore
          | Value.Function _ -> result._val("<function>") |> ignore
          | Value.Tuple _ -> result._val("<tuple>") |> ignore
          | Value.Unit _ -> result._val("()") |> ignore
          | Value.ListComonad _ | Value.ImplicitsComonad _ -> result._val("<comonad>") |> ignore

        let noUi, ui = jq("#" + prefix + "-playground-no-ui"), jq("#" + prefix + "-playground-ui")
        if List.isEmpty inputs then ignore(noUi.show()); ignore(ui.hide()); 
        else ignore(ui.show()); ignore(noUi.hide())        

        for _, i in inputs do i.on("change", fun _ _ -> evaluate(); null).on("keyup", fun _ _ -> evaluate(); null) |> ignore
        evaluate()

        el "button" [ ("class", "btn btn-success") ] [] 
        |> html "<i class='fa fa-play'></i>Run snippet"
        |> click evaluate
        |> appendTo pl |> ignore
    | _ -> ()

// ------------------------------------------------------------------------------------------------
// Create a UI where the user can browse the typing derivation
// ------------------------------------------------------------------------------------------------

  [<JSEmitInline("MathJax.Hub.Queue(['Typeset',MathJax.Hub,{0}]);")>]
  let typeSetElement (el:string) : unit = failwith "!"
  
  [<JSEmitInline("MathJax.Hub.Queue({0});")>]
  let queueAction(f:unit -> unit) : unit = failwith "!"

  let setupTypeDerivation clr prefix kind typed =
    let typetree = Globals.document.getElementById(prefix + "-typetree") :?> HTMLPreElement
    let typetreeTemp = Globals.document.getElementById(prefix + "-typetree-temp") :?> HTMLPreElement

    let rec findSubExpression locations (Typed.Typed(_, e) as te) : Typed<CoeffVars * Coeffect * Type> = 
      match locations, e with
      | [], _ -> te
      | 0::t, (Expr.Let(_, e, _) | Expr.App(e, _) | Expr.Binary(_, e, _) | Expr.Fun(_, e) | Expr.Prev(e) )
      | 1::t, (Expr.Let(_, _, e) | Expr.App(_, e) | Expr.Binary(_, _, e)) ->
          findSubExpression t e
      | _ -> failwith "Invalid path"

    let locations : ref<int list> = ref []

    let rec typeset () =
      let e = findSubExpression (List.rev locations.Value) typed
      let arr : string[] = [| |]
      let root = locations.Value |> List.isEmpty
      MathJax.derivation kind root e arr |> ignore
      let tex = arr.join("").Replace("{\\color{", "{\\color{" + clr)
      typetreeTemp.innerHTML <- "\\[" + tex + "\\]"
      typeSetElement (prefix + "-typetree-temp")

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
        typetree.innerHTML <- typetreeTemp.innerHTML
        typetreeTemp.innerHTML <- ""
          
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

// ------------------------------------------------------------------------------------------------
// Create simple element showing the final typing judgement
// ------------------------------------------------------------------------------------------------

  let setupJudgement clr prefix kind typed =
    let judgement = Globals.document.getElementById(prefix + "-judgement") :?> HTMLPreElement
    let judgementTemp = Globals.document.getElementById(prefix + "-judgement-temp") :?> HTMLPreElement

    let arr : string[] = [| |]
    MathJax.shortJudgement kind typed arr |> ignore
    let tex = arr.join("").Replace("{\\color{", "{\\color{" + clr)
    judgementTemp.innerHTML <- "\\[" + tex + "\\]"
    typeSetElement (prefix + "-judgement-temp")

    queueAction(fun () ->
      judgement.innerHTML <- judgementTemp.innerHTML
      judgementTemp.innerHTML <- "")

// ------------------------------------------------------------------------------------------------
// Display the formatted HTML in a <pre> tag
// ------------------------------------------------------------------------------------------------

  let setupHtmlOutput prefix view kind e =
    let transl = Globals.document.getElementById(prefix + "-" + view) :?> HTMLPreElement
    transl.innerHTML <- Html.print (Html.printExpr kind prefix 0 [] e)
    Globals.eval("setupTooltips()") |> ignore

  let reportError prefix source msg = 
    let error = jq("#" + prefix + "-error")
    let noerror = jq("#" + prefix + "-no-error")
    match msg with
    | Some(err:string) ->
        error.html(err).show() |> ignore
        noerror.hide() |> ignore
        if int error.length = 0 then
          Globals.window.alert("Parsing or type checking failed.\n\n" + (jq("<p>" + err + "</p>").text()) + "\n\nSource:\n" + source)
    | None -> 
        error.hide() |> ignore
        noerror.show() |> ignore

// ------------------------------------------------------------------------------------------------
// Create a UI where the user can browse the typing derivation
// ------------------------------------------------------------------------------------------------

  let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 

  let hasFeature prefix feature = 
     null <> box (Globals.document.getElementById(prefix + "-" + feature))

  let tryGetFeature prefix feature attr = 
    let el = Globals.document.getElementById(prefix + "-" + feature)
    if box el = null then None else 
    let attrval = el.attributes.getNamedItem("data-" + attr)
    if box attrval = null then Some("") else Some(attrval.value)

  let typeCheckSoruce (source:string) kind mode =  
    let (Parsec.Parser lex) = Lexer.lexer
    match lex (List.ofArray (source.ToCharArray())) with
    | Some([], tokens) ->
        let tokensNotWhite = tokens |> filter (function Token.White _ -> false | _ -> true)
        let (Parsec.Parser pars) = Parser.expr ()
        match pars tokensNotWhite with
        | Some([], expr) ->
            TypeChecker.typeCheck (fun _ _ -> Errors.parseError "Unexpected built-in! Built-ins can only appear in translated code.") kind mode expr
            // TODO: Rename all type/coeffect variables before translation to remove clashes
        | _ -> Errors.parseError "Check that everything is syntactically valid. For example, you might be missing the <code>in</code> keyword."
    | _ -> Errors.parseError "Unexpected token. You might be trying to use some unsupported operator or keyword."

  let reload kind mode prefix value = 
//    try
      let typed = typeCheckSoruce value kind mode 
      if hasFeature prefix "output" then
        setupHtmlOutput prefix "output" kind typed

      tryGetFeature prefix "typetree" "tex-color-prefix" 
      |> Option.iter (fun clr -> setupTypeDerivation clr prefix kind typed)

      tryGetFeature prefix "judgement" "tex-color-prefix" 
      |> Option.iter (fun clr -> setupJudgement clr prefix kind typed)

      let transle  = 
        ( if mode = CoeffectMode.Flat then Translation.Flat.translate (Typed((), Expr.Builtin("input", []))) [] typed 
          else Translation.Structural.translate None [] typed ) 
        |> Translation.contract
        |> TypeChecker.typeCheck (Translation.builtins (TypeChecker.coeff typed)) (CoeffectKind.Embedded kind) CoeffectMode.None

      if hasFeature prefix "transl" then
        setupHtmlOutput prefix "transl" kind transle

      if hasFeature prefix "playground" then
        let (Typed(tyinfo, _)) = typed
        setupPlayground prefix kind tyinfo transle
      reportError prefix value None
  //  with e ->
    //  reportError prefix value (Some(e.ToString()))

  let setup kind mode prefix = 
    let btn = Globals.document.getElementById(prefix + "-btn") :?> HTMLButtonElement
    let input = Globals.document.getElementById(prefix + "-input") :?> HTMLTextAreaElement
    btn.addEventListener_click(fun _ -> reload kind mode prefix input.value; null)

  let main () =
    let counter = ref 0
    jq("code[lang*='coeffects']").each(fun _ _ ->
      incr counter
      let lang = jthis().attr("lang")
      let source = jthis().text().Trim()
      let kind = 
        if lang.Contains("impl") then CoeffectKind.ImplicitParams
        elif lang.Contains("df") then CoeffectKind.PastValues
        else failwith ("Unknown kind: " + lang)
      let mode = 
        if lang.Contains("flat") then CoeffectMode.Flat
        elif lang.Contains("struct") then CoeffectMode.Structural
        else failwith ("Unknown mode: " + lang)

      let rec findEditor (je:JQuery) = 
        let ed = unbox<string> (je.data("coeff-editor"))
        if ed <> null then ed
        else findEditor (je.parent())

      if lang.Contains("autoload") then
        let prefix = findEditor (jthis())
        reload kind mode prefix source
      else
        let link = jq("<a><i class=\"fa fa-pencil-square-o\"></i> load</a>")
        jthis().parent().append(link).addClass("pre-play") |> ignore
        link.on("click", fun _ _ ->
          let prefix = findEditor (jthis())
          reload kind mode prefix source
          jq("#" + prefix + "-input")._val(source) |> ignore
          null) |> ignore

      let typed = typeCheckSoruce source kind mode 
      let prefix = "fmtpre" + (string counter.Value)
      jthis().html(Html.print (Html.printExpr kind prefix 0 [] typed)) |> ignore
      null
    ) |> ignore

    jq(".coeff-demo").each(fun _ _ ->
      let kind = 
        match jthis().data("coeff-kind") :?> string with
        | "implicit" -> CoeffectKind.ImplicitParams
        | "dataflow" -> CoeffectKind.PastValues  
        | _ -> failwith "Unexpected kind"
      let mode = 
        match jthis().data("coeff-mode") :?> string with
        | "flat" -> CoeffectMode.Flat
        | "structural" -> CoeffectMode.Structural
        | _ -> failwith "Unexpected mode"
      let id = jthis().attr("id")

      setup kind mode id
      obj() ) |> ignore
    Globals.eval("setupTooltips()") |> ignore

let script = 
  translate <@ Client.main() @>
  |> sprintf "$(function() { %s })"

let processFile file = 
  let fi = File.ReadAllText(Path.Combine(__SOURCE_DIRECTORY__, "web", file))
  let reg = RegularExpressions.Regex(">>>>(.*?)<<<<", RegularExpressions.RegexOptions.Singleline)
  let counter = ref 0
  reg.Replace(fi,RegularExpressions.MatchEvaluator(fun m -> 
    let md = m.Groups.[1].Value.Split [|'\n'|]
    let drop = md |> Seq.filter (System.String.IsNullOrWhiteSpace >> not) |> Seq.map (Seq.takeWhile ((=) ' ') >> Seq.length) |> Seq.min
    let md = md |> Seq.map (fun s -> if System.String.IsNullOrWhiteSpace s then s else s.Substring(drop)) |> String.concat "\n"
    let doc = FSharp.Literate.Literate.ParseMarkdownString(md)
    incr counter
    FSharp.Literate.Literate.WriteHtml(doc, prefix=sprintf "s%d" counter.Value, lineNumbers=false) ))

let app = 
  choose 
    [ path "/" >>= request (fun r -> Successful.OK (processFile "index.html"))
      path "/about" >>= request (fun r -> Successful.OK (processFile "about.html"))
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