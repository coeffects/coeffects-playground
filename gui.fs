// ------------------------------------------------------------------------------------------------
// User interface integration
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Gui

open FunScript
open FunScript.TypeScript
open System.Text
open Coeffects
open Coeffects.Ast
open Coeffects.Pretty
open Coeffects.Evaluation

// ------------------------------------------------------------------------------------------------
// Calling native JavaScript functions
// ------------------------------------------------------------------------------------------------

[<JSEmitInline("$(this)")>]
let jthis() : JQuery = failwith "!"

[<JSEmitInline("$({0})")>]
let jq s : JQuery = failwith "!"

[<JSEmitInline("setLiveChartFunction({0},{1},{2},{3})")>]
let setLiveChartFunction (prefix:string) (xl:int) (yl:int) (f:float[] -> float[] -> float) = failwith "!"

[<JSEmitInline("MathJax.Hub.Queue(['Typeset',MathJax.Hub,{0}]);")>]
let typeSetElement (el:string) : unit = failwith "!"
  
[<JSEmitInline("MathJax.Hub.Queue({0});")>]
let queueAction(f:unit -> unit) : unit = failwith "!"


// ------------------------------------------------------------------------------------------------
// Playgrounds: Create a UI where the user can enter inputs and run the translated program
// ------------------------------------------------------------------------------------------------

// Simple DSL for producing HTML
let el s (attrs:list<string*string>) children = 
  let jp = attrs |> List.fold (fun (j:JQuery) (k, v) -> j.attr(k, v)) (jq("<" + s + " />"))
  children |> List.fold (fun (p:JQuery) (c:JQuery) -> p.append(c)) jp
let css (attrs:list<string*string>) (j:JQuery) = 
  attrs |> List.fold (fun (j:JQuery) (k, v) -> j.css(k, v)) j
let html (s:string) (j:JQuery) = j.html(s)
let appendTo (p:JQuery) (j:JQuery) = j.appendTo(p)
let click (f:unit -> unit) (j:JQuery) = j.click(fun _ -> f(); obj())
let cls (s:string) (j:JQuery) = j.addClass(s)

/// Generates a table with groups of inputs specified by `groups` and appends it to the `pl` element
let inputTable prefix pl groups = 
  let fg = el "table" [] [] |> appendTo pl
  let inputs = 
    groups |> List.map (List.mapi (fun i name ->
      let input = el "input" [ ("type","text"); ("placeholder", "0"); ("class","form-control" + (if i = 0 then " start" else "")) ] []
      let label = el "td" [] [] |> html ("<code>" + name + "</code> =") |> cls "label"
      el "tr" [] [ label; el "td" [] [input] ] |> appendTo fg |> ignore
      input ))
  let result =
    let input = el "input" [ ("type","text"); ("disabled", "disabled"); ("placeholder", "0"); ("class","form-control") ] []
    let label = el "td" [] [] |> html ("<code>result</code> =") |> cls "label"
    el "tr" [] [ label; el "td" [] [input] ] |> cls "result" |> appendTo fg |> ignore
    input

  let noUi, ui = jq("#" + prefix + "-playground-no-ui"), jq("#" + prefix + "-playground-ui")
  if List.forall List.isEmpty inputs then ignore(noUi.show()); ignore(ui.hide()); 
  else ignore(ui.show()); ignore(noUi.hide())
  inputs, result

/// Returns textual representation of a result (if it is tuple or number)
let rec formatResult res =
  match res with 
  | Value.Number n -> string n
  | Value.Function _ -> "<function>"
  | Value.Tuple vs -> "(" + String.concat ", " (List.map formatResult vs) + ")"
  | Value.Unit _ -> "()"
  | Value.ListComonad _ | Value.ImplicitsComonad _ -> "<comonad>"

/// Returns None if any of the calls to `f` fail, otherwise returns `Some` with results
let tryMap f xs =
  let rec loop acc xs =
    match xs with 
    | [] -> Some(List.rev acc)
    | x::xs ->
        match f x with
        | None -> None
        | Some v -> loop (v::acc) xs
  loop [] xs

/// Setup live chart - call `setLiveChartFunction` with a JS-compatible function
/// that takes an array of X and Y coordinates and produces a new value.
let setupLiveChart prefix kind mode (Typed(tyinfo, typed)) transle =
  let noUi, ui = jq("#" + prefix + "-livechart-no-ui"), jq("#" + prefix + "-livechart-ui")        
  match kind, tyinfo with
  | CoeffectKind.PastValues, (_, _, Type.Funcs([(_, Coeffect.Past xl), _; (_, Coeffect.Past yl), _], _)) ->
      Trace.event "play" "setup-live-chart" prefix
      let evaluate xs ys = 
        let args = 
          [ Value.Tuple [Value.ListComonad (xs |> List.ofArray |> List.map Value.Number)]
            Value.Tuple [Value.ListComonad (ys |> List.ofArray |> List.map Value.Number)] ]
        let sinput = Value.Tuple []
        let res = 
          match eval { Kind = kind; Variables = Map.ofSeq ["sinput", sinput]; Mode = mode } transle with
          | Value.Functions f -> f args
          | _ -> failwith "Expected function"
        match res with Value.Number n -> n | _ -> failwith "Not a number"
      setLiveChartFunction prefix (1+xl) (1+yl) evaluate
      ignore(ui.show()); ignore(noUi.hide())
  | _ -> 
      ignore(noUi.show()); ignore(ui.hide()); 

/// Setup playground with table of inputs (for implicit param values or past values)
let setupPlayground prefix kind mode (Typed(tyinfo, typed)) transle = 
  let playground = Globals.document.getElementById(prefix + "-playground") :?> HTMLPreElement
  playground.innerHTML <- "";
  match kind, tyinfo with
  | CoeffectKind.PastValues, (_, _, f) ->
      // Create groups of inputs for each varaible of the input function
      // First, we try to guess the variable names
      Trace.event "play" "setup-past-values" prefix
      let inputs = match f with Type.Funcs(inputs, _) -> inputs | _ -> []
      let names = 
        match typed with   
        | Expr.Let(TypedPat(_, Pattern.Var s1), Typed(_, Expr.Funs(inputs, _)), Typed(_, Expr.Var s2)) when s1 = s2 ->
            inputs |> tryMap (function TypedPat(_, Pattern.Var n) -> Some n | _ -> None)
        | Expr.Funs(inputs, _) -> 
            inputs |> tryMap (function TypedPat(_, Pattern.Var n) -> Some n | _ -> None)
        | _ -> None
      let names = defaultArg names (List.mapi (fun i _ -> "var" + string i) inputs)

      // Generate the inputs & output table
      let inputs = List.map2 (fun n coeff -> 
        match coeff with 
        | ((_, Coeffect.Past k), _) -> [ for i in 0 .. k -> n + "[" + string i + "]" ]
        | _ -> failwith "expected past") names inputs
      let pl = jq(playground)
      let inputs, result = inputTable prefix pl inputs

      // When input changes, re-evaluate & display the result!
      let evaluate () = 
        Trace.event "play" "eval-past-values" prefix
        let sinput = Value.Tuple []
        let res = 
          match eval { Kind = kind; Variables = Map.ofSeq ["sinput", sinput]; Mode = mode } transle with
          | Value.Functions f -> 
              let args = 
                [ for g in inputs -> Value.Tuple [Value.ListComonad [ for i in g -> Value.Number(1.0 * unbox(i._val())) ]] ]
              f args
          | res -> res
        result._val(formatResult res) |> ignore

      for g in inputs do 
        for i in g do i.on("change", fun _ _ -> 
          evaluate(); null).on("keyup", fun _ _ -> evaluate(); null) |> ignore
      evaluate()

  | CoeffectKind.ImplicitParams, (_, c, _) ->
      // Create a table with inputs for all unbound implicit parameters
      Trace.event "play" "setup-implicit-params" prefix
      let coeffs = Solver.ImplicitParams.evalCoeffect Map.empty c |> Set.toList
      let pl = jq(playground)
      let inputs, result = inputTable prefix pl [[ for c in coeffs -> "?" + c ]]
      let inputs = List.head inputs
         
      // When input changes, re-evaluate & display the result!
      let evaluate () = 
        Trace.event "play" "eval-implicit-params" prefix
        let input = Value.ImplicitsComonad(Value.Unit, Map.ofList [ for c, i in List.zip coeffs inputs -> c, Value.Number(1.0 * unbox(i._val())) ])
        let res = eval { Kind = kind; Variables = Map.ofSeq ["finput", input]; Mode = mode } transle // Flat input
        result._val(formatResult res) |> ignore

      for i in inputs do 
        i.on("change", fun _ _ -> evaluate(); null).on("keyup", fun _ _ -> evaluate(); null) |> ignore
      evaluate()

  | _ -> ()

// ------------------------------------------------------------------------------------------------
// Create a UI where the user can browse the typing derivation
// ------------------------------------------------------------------------------------------------

let setupTypeDerivation clr prefix kind typed =
  let typetree = jq("#" + prefix + "-typetree")
  let typetreeTemp = jq("#" + prefix + "-typetree-temp")
  let navigColor = typetree.data("navigation-color") :?> string
  let currentColor = typetree.data("current-color") :?> string

  /// Find a sub-expression matching the specified path
  /// (the path is a list of numbers indicating index of sub-expression)
  let rec findSubExpression locations (Typed.Typed(_, e) as te) : Typed<CoeffVars * Coeffect * Type> = 
    match locations, e with
    | [], _ -> te
    | 0::t, (Expr.Let(_, e, _) | Expr.App(e, _) | Expr.Binary(_, e, _) | Expr.Fun(_, e) | Expr.Prev(e) )
    | 1::t, (Expr.Let(_, _, e) | Expr.App(_, e) | Expr.Binary(_, _, e)) ->
        findSubExpression t e
    | _ -> failwith "Invalid path"

  /// Remembers the current path
  let locations : ref<int list> = ref []

  /// Typeset the expression using the current location 
  let rec typeset () =
    let e = findSubExpression (List.rev locations.Value) typed
    let arr : string[] = [| |]
    let root = locations.Value |> List.isEmpty
    MathJax.derivation kind root e arr |> ignore
    let tex = arr.join("").Replace("{\\color{", "{\\color{" + clr)
    typetreeTemp.html("\\[" + tex + "\\]") |> ignore
    typeSetElement (prefix + "-typetree-temp")

    /// Generate path for the specified 'jo' element
    let getNewPath (jo:JQuery) =
      let index = jq("#" + prefix + " .mtable").index(jo)
      let length = jq("#" + prefix + " .mtable").length

      // There is no (...) in conclusion when we're in the root
      let current = if root then length - 1.0 else length - 2.0
      if index = current then
        // We are here currently
        true, locations.Value
      elif index > current then
        // Drop one from path (going to conclusions)
        false, locations.Value |> List.tail
      else 
        // Add new to the path (going to assumptions)
        false, (int index) :: locations.Value

    /// Highlighting effect
    let highlight (jo:JQuery) (thisClr:string) (currClr:string) = 
      let current, path = getNewPath jo
      let path = List.rev path
      let id = prefix + "-p-" + (String.concat "-" (List.map string path))
      let clr = if current then currClr else thisClr
      jq("#" + id).css("backgroundColor", clr) |> ignore
      jo.css("backgroundColor", clr) |> ignore
  
    // Invoke the type-setting - using hidden TEMP element & then copy
    queueAction(fun () ->
      typetree.html(typetreeTemp.html()) |> ignore
      typetreeTemp.html("") |> ignore
          
      jq("#" + prefix + " .mtable").css("cursor", "pointer") |> ignore
      let currIndex = jq("#" + prefix + " .mtable").length - (if root then 1.0 else 2.0)
      jq("#" + prefix + " .mtable").eq(currIndex).css("cursor","default") |> ignore

      jq("#" + prefix + " .mtable")
        .on("click", fun e o ->
          jq("#" + prefix + " .p-span").css("backgroundColor", "transparent") |> ignore
          locations.Value <- snd (getNewPath (jthis()))
          Trace.event "typing" "navigate" (Array.ofList locations.Value)
          typeset ()
          box () )
        .on("mouseenter", fun e o ->
          highlight (jthis()) navigColor currentColor
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
// Helpers for detecting what to do (features) and others
// ------------------------------------------------------------------------------------------------

// FunScript workaround (filter reverses the list)
let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 

/// Display the formatted HTML in a <pre> tag
let setupHtmlOutput prefix compact view kind e =
  let transl = Globals.document.getElementById(prefix + "-" + view) :?> HTMLPreElement
  transl.innerHTML <- Html.print (Html.printExpr compact kind prefix 0 [] e)
  Globals.eval("setupTooltips()") |> ignore

/// Display error (when msg is Some) or hide error (when msg=None)
let reportError prefix source msg = 
  let error = jq("#" + prefix + "-error")
  let noerror = jq("#" + prefix + "-no-error")
  match msg with
  | Some(err:string) ->
      Trace.event "error" "report" err
      error.html(err).show() |> ignore
      noerror.hide() |> ignore
      if int error.length = 0 then
        Globals.window.alert("Parsing or type checking failed.\n\n" + (jq("<p>" + err + "</p>").text()) + "\n\nSource:\n" + source)
  | None -> 
      error.hide() |> ignore
      noerror.show() |> ignore

/// Check whether a feature is part of this 'playground'
let hasFeature prefix feature = 
    null <> box (Globals.document.getElementById(prefix + "-" + feature))

/// Get some data attribute attached to a feature
let tryGetFeature prefix feature attr = 
  let el = Globals.document.getElementById(prefix + "-" + feature)
  if box el = null then None else 
  let attrval = el.attributes.getNamedItem("data-" + attr)
  if box attrval = null then Some("") else Some(attrval.value)

/// Type check the source code and return AST
let typeCheckSoruce (source:string) kind mode =  
  let (Parsec.Parser lex) = Lexer.lexer
  match lex (List.ofArray (source.ToCharArray())) with
  | Some([], tokens) ->
      let tokensNotWhite = tokens |> filter (function Token.White _ -> false | _ -> true)
      let (Parsec.Parser pars) = Parser.expr ()
      match pars tokensNotWhite with
      | Some([], expr) ->
          TypeChecker.typeCheck (fun _ _ -> Errors.parseError "Unexpected built-in! Built-ins can only appear in translated code.") kind mode expr
      | _ -> Errors.parseError "Check that everything is syntactically valid. For example, you might be missing the <code>in</code> keyword."
  | _ -> Errors.parseError "Unexpected token. You might be trying to use some unsupported operator or keyword."


// ------------------------------------------------------------------------------------------------
// Main UI integration - format source, handle reloads & display various results
// ------------------------------------------------------------------------------------------------

/// Type-checks & translates source code and performs various actions
/// depending on what HTML elements with 'prefix' are available
let reload kind mode prefix value = 
  try
    // There is a <select> choosing mode & kind and we need to switch it to the right setting
    if hasFeature prefix "langchooser" then
      let mode = match mode with CoeffectMode.Flat -> "flat" | _ -> "structural"
      let kind = match kind with CoeffectKind.ImplicitParams -> "implicit" | _ -> "dataflow"
      jq("#" + prefix + "-langchooser")._val(mode + "-" + kind) |> ignore
        
    // Type check and display HTML - not compact expands 'let' and curried functions
    let typed = typeCheckSoruce value kind mode 
    if hasFeature prefix "output" then
      setupHtmlOutput prefix true "output" kind typed
    if hasFeature prefix "longoutput" then
      setupHtmlOutput prefix false "longoutput" kind typed

    // Type set typing derivation or current judgement
    tryGetFeature prefix "typetree" "tex-color-prefix" 
    |> Option.iter (fun clr -> setupTypeDerivation clr prefix kind typed)
    tryGetFeature prefix "judgement" "tex-color-prefix" 
    |> Option.iter (fun clr -> setupJudgement clr prefix kind typed)

    // Translate the source code & display translation
    let transle = Translation.translate mode kind typed 
    if hasFeature prefix "transl" then
      setupHtmlOutput prefix true "transl" kind transle

    // Setup interactive playground or livechart
    if hasFeature prefix "playground" then
      setupPlayground prefix kind mode typed transle
    if hasFeature prefix "livechart" then
      setupLiveChart prefix kind mode typed transle

    // Nothing went wrong, that's good :)
    reportError prefix value None
  with e ->
    // Something went wrong, report an error
    reportError prefix value (Some(e.ToString()))


/// Called when the page loads. Formats <pre> elements and registers
/// handlers for all 'coeff-demo' elements (containing various features)
let main () =
  // Format all <pre> tags containing coeffect source code
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
      // Autoload the source code in associated editor
      let prefix = findEditor (jthis())
      reload kind mode prefix source
    else
      // Create a link for loading the source code
      let link = jq("<a><i class=\"fa fa-pencil-square-o\"></i> load</a>")
      jthis().parent().append(link).addClass("pre-play") |> ignore
      link.on("click", fun _ _ ->
        let prefix = findEditor (jthis())
        Trace.event "code" "load" (Trace.data [| ("prefix",prefix); ("source",source) |])
        reload kind mode prefix source
        jq("#" + prefix + "-input")._val(source) |> ignore
        null) |> ignore

    // Type check the source and set formatted HTML
    let typed = typeCheckSoruce source kind mode 
    let prefix = "fmtpre" + (string counter.Value)
    jthis().html(Html.print (Html.printExpr true kind prefix 0 [] typed)) |> ignore
    null
  ) |> ignore

  // Setup handlers for all plagrounds in the document
  jq(".coeff-demo").each(fun _ _ ->
    let prefix = jthis().attr("id")
    let kindMode = jthis().data("coeff-kind") :?> string, jthis().data("coeff-mode") :?> string 
    let reloadHandler value =
      // Get kind and mode - either from langchooser <select> or from data attribute
      let kindStr, modeStr =
        if hasFeature prefix "langchooser" then
          let kindMode = jq("#" + prefix + "-langchooser")._val() :?> string
          kindMode, kindMode
        else kindMode
      let kind = 
        if kindStr.Contains "implicit" then CoeffectKind.ImplicitParams
        elif kindStr.Contains "dataflow" then CoeffectKind.PastValues  
        else failwith "Unexpected kind"
      let mode = 
        if modeStr.Contains "flat" then CoeffectMode.Flat
        elif modeStr.Contains "structural" then CoeffectMode.Structural
        else failwith "Unexpected mode"
      Trace.event "code" "check" (Trace.data [| ("prefix",prefix); ("mode",modeStr); ("kind",kindStr); ("source",value) |])
      reload kind mode prefix value

    let btn = Globals.document.getElementById(prefix + "-btn") :?> HTMLButtonElement
    let input = Globals.document.getElementById(prefix + "-input") :?> HTMLTextAreaElement
    btn.addEventListener_click(fun _ -> reloadHandler input.value; null)
    obj() ) |> ignore

  // Replce 'title' with nice HTML tool tips
  Globals.eval("setupTooltips()") |> ignore
