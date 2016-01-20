// ------------------------------------------------------------------------------------------------
// Pretty printer for producing HTML and MathJax versions 
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Pretty

open FunScript
open FunScript.TypeScript
open Coeffects
open Coeffects.Ast

/// JavaScript extensions for working with arrays
type 'T``[]`` with
  [<JSEmitInline("{0}.push({1})")>]
  member x.push(v:'T) : unit = failwith "!"

/// Primitive coeffect to render can be set of resources, no. of past values
[<RequireQualifiedAccess>]
type PrimitiveCoeffect = 
  | PastValues of int
  | ResourceSet of list<string * Type>

/// Helper for let binding
let (|Let|) a x = a, x

/// Turns implicit parameter coeffects into a list of implicit params
let rec flattenCoeffects kind c = 
  let rec flattenImplicits c = 
    match c with
    | Coeffect.None -> []
    | Coeffect.Ignore | Coeffect.Use -> []
    | Coeffect.ImplicitParam(s, t) -> [s, t]
    | Coeffect.Merge(c1, c2) | Coeffect.Split(c1, c2) | Coeffect.Seq(c1, c2) -> 
        flattenImplicits c1 @ flattenImplicits c2
    | Coeffect.Past _ -> Errors.unexpected "Unexpected <code>Coeffect.Past</code> when flattening dataflow coeffects in <code>flattenCoeffects</code>."
    | Coeffect.Variable _ -> Errors.unexpected "Unresolved <code>Coeffect.Variable</code> when flattening dataflow coeffects in <code>flattenCoeffects</code>."
  let rec flattenPast c = 
    match c with
    | Coeffect.None -> 0
    | Coeffect.Ignore | Coeffect.Use -> 0  
    | Let min (op, Coeffect.Merge(c1, c2))
    | Let max (op, Coeffect.Split(c1, c2))
    | Let (+) (op, Coeffect.Seq(c1, c2)) -> op (flattenPast c1) (flattenPast c2)
    | Coeffect.Past(n) -> n
    | Coeffect.ImplicitParam _ -> Errors.unexpected "Unexpected <code>Coeffect.ImplicitParam</code> when flattening implicit parameters coeffects in <code>flattenCoeffects</code>."
    | Coeffect.Variable _ -> Errors.unexpected "Unresolved <code>Coeffect.Variable</code> when flattening implicit parameter coeffects in <code>flattenCoeffects</code>."
    | _ -> Errors.unexpected "Unresolved coeffectvalue when flattening dataflow coeffects in <code>flattenCoeffects</code>."
  match kind with
  | CoeffectKind.ImplicitParams -> PrimitiveCoeffect.ResourceSet (flattenImplicits c)
  | CoeffectKind.PastValues -> PrimitiveCoeffect.PastValues (flattenPast c)
  | CoeffectKind.Embedded k -> flattenCoeffects k c

/// Returns the precedence of an expression - we need to wrap sub-expressions in brackets they 
/// have smaller precedence. This also returns adjustments for the left/right sub-expression.
/// We add 1 on the left when entering right-associative operations (and vice versa) to make 
/// sure we bracket  (1 ^ 2) ^ 3  and  1 + (2 + 3).
///
///    +----------+------+
///    | Expr     | Prec |
///    +----------+------+
///    | prev     |  60  | 
///    | @        |  50  |
///    | ^        |  40  |
///    | *, /     |  30  |
///    | +, -     |  20  |
///    | <tuple>  |  10  |
///    | let, fun |  00  |
///    +----------+------+
///
let precedence expr = 
  let prec, (lfix, rfix) =
    match expr with
    | Expr.Builtin _ | Expr.Var _ | Expr.QVar _ | Expr.Number _ -> 100, (0, 0)
    | Expr.Prev _ -> 60, (0, 0)
    | Expr.App _ -> 50, (0, 1)
    | Expr.Binary("^", _, _) -> 40, (1, 0)
    | Expr.Binary("/", _, _) | Expr.Binary("*", _, _) -> 30, (0, 1)
    | Expr.Binary("+", _, _) | Expr.Binary("-", _, _) -> 20, (0, 1)
    | Expr.Binary _ -> 20, (0, 1)
    | Expr.Tuple _ -> 10, (1, 1)
    | Expr.Fun _ | Expr.Let _ -> 00, (0, 0)
  prec, (prec + lfix, prec + rfix)

// ------------------------------------------------------------------------------------------------
// Pretty printer that produces HTML inside <pre> tag
// ------------------------------------------------------------------------------------------------

module Html = 

  /// Simple pretty printer - for Text, we append strings to array to
  /// make running it in JavaScript a bit faster (one would hope)
  type Printer = 
    | Text of (string[] -> unit)
    | Append of Printer * Printer
    | Wrap of Printer
    | Newline 

  let text s = Text(fun sb -> sb.push(s))
  let (++) p1 p2 = Append(p1, p2)
  let wrap p = Wrap(p)
  let newline = Newline

  /// Run a printing function inline
  let inl f = 
    let arr : string[] = [| |]
    f arr
    arr.join("")

  /// Run the pretty printer!
  let print p =
    let sb : string[] = [| |]
    let rec multiline p =
      match p with 
      | Printer.Newline -> true
      | Printer.Append(p1, p2) -> multiline p1 || multiline p2
      | _ -> false
    let rec loop indent p = 
      match p with 
      | Printer.Text f -> f sb
      | Printer.Append(p1, p2) -> loop indent p1; loop indent p2
      | Printer.Newline -> sb.push("\n" + indent)
      | Printer.Wrap(p) -> 
          if multiline p then
            sb.push("\n  " + indent)
            loop ("  " + indent) p
          else loop indent p    

    loop "" p
    sb.join("")

  /// Format <span "attrs"> "body" </span>
  let span attrs body = Text(fun sb ->
    sb.push("<span")
    for k, v in attrs do 
      sb.push(" ")
      sb.push(k)
      sb.push("='")
      sb.push(v)
      sb.push("'")
    sb.push(">")
    sb.push(body)
    sb.push("</span>"))

  /// Build printer for a pattern
  let rec printPat kind (TypedPat((_, _, t), pat)) = 
    let title () = inl (printTyp kind t)
    match pat with
    | Pattern.Var(s) -> span ["title",title (); "class","i"] s
    | Pattern.QVar(s) -> span ["title",title (); "class","i"] ("?" + s)
    | Pattern.Tuple(pats) -> 
        let body = pats |> List.map (printPat kind) |> List.reduce (fun p1 p2 -> p1 ++ text ", " ++ p2) 
        text "(" ++ body ++ text ")" 


  /// Print coeffect annotation to the given array
  and printCoeff kind coeffs (sb:string[]) =
    let mutable first = true
    for n, t in coeffs do
      if first then first <- false
      else sb.push(", ")
      sb.push("?")
      sb.push(n)
      sb.push(":")
      sb |> printTyp kind t

  /// Print type annotation to the given array
  and printTyp kind typ (sb:string[]) = 
    match typ with 
    | Type.StructuralComonad(cls, t) ->
        sb.push("C [")
        let mutable first = true
        for cl in cls do
          if first then first <- false 
          else sb.push(", ")
          match flattenCoeffects kind cl with
          | PrimitiveCoeffect.PastValues n -> 
              sb.push(string n)
          | PrimitiveCoeffect.ResourceSet coeffs -> 
              sb.push("{ ")
              printCoeff kind coeffs sb
              sb.push(" }")
        sb.push("] ")
        printTyp kind t sb

    | Type.FlatComonad(cl, t) ->
        sb.push("C ")
        match flattenCoeffects kind cl with
        | PrimitiveCoeffect.PastValues 0 
        | PrimitiveCoeffect.ResourceSet [] -> ()
        | PrimitiveCoeffect.PastValues n -> 
            sb.push(string n + " ")
        | PrimitiveCoeffect.ResourceSet coeffs -> 
            sb.push(" { ")
            printCoeff kind coeffs sb
            sb.push(" } ")
        printTyp kind t sb

    | Type.Variable s -> sb.push(s)
    | Type.Tuple(ts) ->
        sb.push("(")
        printTyp kind (List.head ts) sb |> ignore
        for t in List.tail ts do
          sb.push(" * ")
          printTyp kind t sb |> ignore
        sb.push(")")
        
    | Type.Func((cf, cs), t1, t2) -> 
        sb.push("(")
        printTyp kind t1 sb
        let c = 
          if cf = Coeffect.None then cs 
          elif cs = Coeffect.None then cf
          else Errors.unexpected "Pretty printer cannot format coeffect langauge expression with mixed flat and structural coeffects."
        match flattenCoeffects kind c with
        | PrimitiveCoeffect.PastValues 0 
        | PrimitiveCoeffect.ResourceSet [] ->
            sb.push(" -&gt; ")
        | PrimitiveCoeffect.PastValues n -> 
            sb.push(" -{ " + string n + " }-&gt; ")
        | PrimitiveCoeffect.ResourceSet coeffs -> 
            sb.push(" -{ ")
            printCoeff kind coeffs sb
            sb.push(" }-&gt; ")
        printTyp kind t2 sb
        sb.push(")")
    | Type.Primitive s -> sb.push(s)

  let withId prefix path p = 
    let id = "-p-" + String.concat "-" (List.rev (List.map string path))
    text ("<span class='p-span' id='" + prefix + id + "'>") ++ p ++ text "</span>"

  let sep items sep = 
    List.fold (fun st it -> st ++ sep ++ it) (List.head items) (List.tail items)

  /// Print coeffect language expression
  let rec printExpr kind prefix prec path (Typed.Typed((_, coeff, typ), expr)) =

    // Wrap in parentheses if this expression has lower precedence
    let thisPrec, (lPrec, rPrec) = precedence expr 
    let wrapParens = 
      if thisPrec >= prec then id
      else fun p -> text "(" ++ p ++ text ")"

    // Generate the body and then call wrapping functions
    ( match expr with
      | Expr.Var(s) -> span ["title", inl (printTyp kind typ); "class","i"] s 
      | Expr.Builtin(s, _) -> span ["title", inl (printTyp kind typ); "class","op"] s 
      | Expr.QVar(s) -> span ["title", inl (printTyp kind typ); "class","i"] ("?" + s)
      | Expr.Number(n) -> span ["class","n"] (string n)
      | Expr.Prev(e) -> span ["class","k"] "prev" ++ text " " ++ printExpr kind prefix thisPrec (0::path) e
      | Expr.Funs(pats, body) -> 
          let tin = match typ with Type.Func(_, tin, _) -> tin | _ -> Errors.unexpected "Expected a type <code>Type.Func</code> when pretty printing a function value."
          span ["class","k"] "fun" ++ text " " ++ 
            sep (List.map (printPat kind) pats) (text " ") ++ text " " ++
            span ["class","k"] "-&gt;" ++ text " " ++
            wrap (printExpr kind prefix thisPrec (0::path) body)
      | Expr.Lets(pats, (Typed.Typed((_, coeff, vtyp), _) as arg), body) -> 
          span ["class","k"] "let" ++ text " " ++ sep (List.map (printPat kind) pats) (text " ") ++ text " " ++
            span ["class","op"] "=" ++ text " " ++ wrap (printExpr kind prefix thisPrec (0::path) arg) ++ text " " ++
            span ["class", "k"] "in" ++ newline ++ printExpr kind prefix thisPrec (1::path) body

      | Expr.App(e1, e2) ->
          printExpr kind prefix lPrec (0::path) e1 ++ text " " ++ 
            printExpr kind prefix rPrec (1::path) e2

      | Expr.Binary(op, e1, e2) -> 
          printExpr kind prefix lPrec (0::path) e1 ++ text " " ++ span ["class","op"] op ++ 
            text " " ++ printExpr kind prefix rPrec (1::path) e2

      | Expr.Tuple(es) ->
          es |> List.mapi (fun i e -> printExpr kind prefix lPrec (i::path) e)
             |> List.reduce (fun p1 p2 -> p1 ++ text ", " ++ p2) 
      | Expr.Fun _ -> Errors.unexpected "Failed to format <code>Expr.Fun</code>. This case should be covered by <code>Funs</code>."
      | Expr.Let _ -> Errors.unexpected "Failed to format <code>Expr.Let</code>. This case should be covered by <code>Lets</code>." )

    |> wrapParens |> withId prefix path
    
 
// ------------------------------------------------------------------------------------------------
// Pretty printer that produces MathJax judgements
// ------------------------------------------------------------------------------------------------

module MathJax = 

  /// Add a separator 's' between every two items in 'fs'
  let sep s fs (ar:string[]) = 
    let mutable first = true
    for f in fs do
      if first then first <- false
      else ignore (s ar) 
      ignore (f ar)
    ar

  /// Appends string to the mutable JS array of strings
  let inl s (arr:string[]) = 
    arr.push(s); arr

  /// Appends string as a colored keyword
  let kvd s (arr:string[]) = 
    arr |> inl ("{\\color{kvd}\\text{" + s + "}}")

  /// Appends integer as a colored number
  let num n (arr:string[]) = 
    arr |> inl ("{\\color{num} " + string n + "}")

  /// Appends string as a colored operator
  let operator op (arr:string[]) = 
    arr |> inl ("\,{\\color{op} " + op + "}\,")

  /// Formats and appends pattern
  let rec pattern (TypedPat(_, pat)) strs = 
    match pat with 
    | Pattern.Var v -> strs |> inl v
    | Pattern.QVar v -> strs |> inl ("?" + v)
    | Pattern.Tuple(pats) -> strs |> inl "(" |> sep (inl ", ") (List.map pattern pats) |> inl ")" 

  /// If the formatting function 'f' produces less than 'n' segments, we use 
  /// whetever it returns, otherwise we use the function 'g' instead.
  let limit n f g (arr:string[]) =
    let l1 = arr.Length
    let _ = f arr
    if arr.Length <= l1 + n then arr
    else 
      let _ = arr.splice(float l1, float (arr.Length - l1)) 
      g arr

  /// Format an expression
  let rec expr limLength prec (Typed.Typed((_, c, t),e)) (ar:string[]) = 
    // Wrap in parentheses if this expression has lower precedence
    let expr = expr limLength
    let thisPrec, (lPrec, rPrec) = precedence e
    let close = 
      if thisPrec >= prec then id
      else 
        ar.push("(")
        (fun (ar:string[]) -> ar.push(")"); ar)
    // Format the expression and then close the opening bracket (if opened)
    ( match e with
      | Expr.Builtin _ -> failwith "TODO"
      | Expr.Tuple(es) ->
         ar |> sep (inl ", ") (List.map (expr lPrec) es)
      | Expr.Var(v) -> ar |> inl v
      | Expr.QVar(v) -> ar |> inl ("?" + v)
      | Expr.Number(n) -> ar |> num n
      | Expr.Prev(e) -> ar |> kvd "prev" |> inl "~" |> limit limLength (expr thisPrec e) (inl "\\ldots")
      | Expr.App(e1, e2) ->
         ar |> expr lPrec e1 |> inl "~" |> expr rPrec e2
      | Expr.Let(pat, arg, body) ->
         ar |> kvd "let" |> inl "~" |> pattern pat |> operator "=" 
            |> limit limLength (expr thisPrec arg) (inl "\\ldots") |> inl "~" |> kvd "in" |> inl "~" 
            |> limit limLength (expr thisPrec body) (inl "\\ldots")
      | Expr.Binary(op, e1, e2) -> 
         ar |> limit limLength (expr lPrec e1) (inl "\\ldots") |> operator op
            |> limit limLength (expr rPrec e2) (inl "\\ldots")
      | Expr.Fun(pat, body) ->
         ar |> kvd "fun" |> inl "~" |> pattern pat |> inl "\\rightarrow "
            |> limit limLength (expr thisPrec body) (inl "\\ldots") )
    |> close

  /// Format the free-variable context
  let rec vars kind (vars:CoeffVars) (ar:string[]) = 
    let mutable first = true
    for v, (_, t) in Map.toList vars do
      if first then first <- false
      else ar.push(", ")
      ar.push(v)
      ar.push("\!:\!")
      typ kind true t ar |> ignore
    ar      

  /// Format the coeffect (either set of implicit parameters or a number)
  and coeff kind short c (ar:string[]) =
    ar.push("{\\color{coeff} ")
    match flattenCoeffects kind c with
    | PrimitiveCoeffect.PastValues n ->
        ar.push(string n)
    | PrimitiveCoeffect.ResourceSet impls ->
      let mutable first = true
      for v, t in impls do
        if first then first <- false
        else ar.push(", ")
        ar.push("?" + v)
        if not short then 
          ar.push("\!:\!")
          typ kind false t ar |> ignore
    ar |> inl"}"

  /// Format a type (optionally with color - but we don't do this for types inside coeffects)
  and typ kind colored t (ar:string[]) =
    if colored then ar.push("{\\color{typ} ")
    match t with
    | Type.FlatComonad(c, t) ->
        ar |> inl "C^{" |> coeff kind true c |> inl "}" |> ignore
    | Type.StructuralComonad(c, t) ->
        ar |> inl "C^{\\langle" |> sep (inl ",") (List.map (coeff kind true) c) |> inl "\\rangle}" |> ignore
    | Type.Tuple(ts) ->
        ar |> inl "(" |> sep (inl "\\ast") (List.map (typ kind colored) ts) |> inl ")" |> ignore
    | Type.Func((cf, cs), t1, t2) -> 
        let c = 
          if cf = Coeffect.None then cs 
          elif cs = Coeffect.None then cf
          else Errors.unexpected "Pretty printer cannot format coeffect langauge expression with mixed flat and structural coeffects."
        ar |> typ kind colored t1 |> inl "\\xrightarrow{" |> coeff kind true c 
           |> inl "}" |> typ kind colored t2 |> ignore
    | Type.Primitive(s) -> ar |> inl ("\\text{" + s + "}") |> ignore
    | Type.Variable(s) -> ar |> inl ("`" + s) |> ignore
    if colored then ar |> inl "}" else ar

  /// Format flat or structural coeffects in the typing judgement (before \vdash)
  let coeffs kind cvars c ar =
    if c <> Coeffect.None then coeff kind false c ar
    else
      let mutable first = true
      if not (Map.isEmpty cvars) then
        ar.push("\\langle")
        for _, (c, _) in Map.toList cvars do
          if first then first <- false
          else ar.push(",")
          coeff kind false c ar |> ignore
        ar.push("\\rangle")
      ar

  /// Format a typing judgement of the form $\Gamma @ c \vdash e : \tau$
  let judgement kind (Typed.Typed((v, c, t), e) as te) (ar:string[]) =
    ar |> vars kind v |> inl "\\,{\\small @}\\," |> coeffs kind v c 
       |> inl "\\vdash " |> expr 8 0 te |> inl ":" |> typ kind true t

  /// Format a typing judgement of the form $\Gamma @ c \vdash e : \tau$
  /// This limits the size of the expression body a bit more than `judgement`.
  let shortJudgement kind (Typed.Typed((v, c, t), e) as te) (ar:string[]) =
    ar |> vars kind v |> inl "\\,{\\small @}\\," |> coeffs kind v c 
       |> inl "\\vdash " |> expr 3 0 te |> inl ":" |> typ kind true t

  /// Wraps the specified formatting function in LaTeX array
  let array f ar = 
    ar |> inl "\\begin{array}{c}" |> f |> inl "\\end{array}" 

  /// Create typing derivation with specified assumptions and conclusion
  let dfrac ups down (ar:string[]) = 
    ar |> inl "\\dfrac{" |> sep (inl "\\quad") ups |> inl "}{"
       |> down |> inl "}"

  /// Generates a judgement containing (...) in the assumptions if there are any
  let typedTree kind (Typed.Typed(_, e) as te) =
    match e with
    | Expr.Fun _ | Expr.App _ | Expr.Binary _ | Expr.Let _ | Expr.Prev _ | Expr.Tuple _ ->
        dfrac [ inl "(\\ldots)" ] (array (judgement kind te))
    | _ -> 
        dfrac [ inl "~" ] (array (judgement kind te))

  /// Generates one step of a typing derivation. When `root <> true`, it also adds
  /// one more note below containing (...) that can be clicked on for going down.
  let derivation kind root (Typed.Typed((v, c, t), e) as te) (ar:string[]) = 
    let conclusion = 
      if root then array (judgement kind te)
      else dfrac [ array (judgement kind te) ] (array (inl "(\\ldots)"))
    match e with
    | Expr.Builtin _ | Expr.Var _ | Expr.QVar _ | Expr.Number _ -> 
        ar |> dfrac [] conclusion
    | Expr.Prev(e) | Expr.Fun(_, e) ->
        ar |> dfrac [ typedTree kind e ] conclusion
    | Expr.App(e1, e2)
    | Expr.Binary(_, e1, e2)
    | Expr.Let(_, e1, e2) ->
        ar |> dfrac [ typedTree kind e1; typedTree kind e2 ] conclusion
    | Expr.Tuple(es) ->
        ar |> dfrac (List.map (typedTree kind) es) conclusion
    
