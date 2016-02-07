#r "packages/FunScript/lib/net40/FunScript.dll"
#r "packages/FunScript/lib/net40/FunScript.Interop.dll"
#r "packages/FunScript.TypeScript.Binding.lib/lib/net40/FunScript.TypeScript.Binding.lib.dll"
#r "packages/FunScript.TypeScript.Binding.jquery/lib/net40/FunScript.TypeScript.Binding.jquery.dll"
#r "bin/Debug/Coeffects.exe"

open System.IO
open Coeffects
open Coeffects.Parser
open Coeffects.Parsec
open Coeffects.Ast
open Coeffects.TypeChecker
open Coeffects.Solver
open Coeffects.Translation


let source = """?fst ?snd"""
let (Parsec.Parser lex) = Lexer.lexer
let tokens = lex (List.ofArray (source.ToCharArray())) |> Option.get |> snd
let tokens' = tokens |> List.filter (function Token.White _ -> false | _ -> true)
let (Parsec.Parser pars) = Parser.expr ()
let expr = pars tokens' |> Option.get |> snd
let builtins1, kind, mode = (fun _ _ -> failwith "!"), CoeffectKind.ImplicitParams, CoeffectMode.Flat
let typed = TypeChecker.typeCheck builtins1 kind mode expr


let builtins2, kind2, mode2 = Translation.builtins (TypeChecker.coeff typed), CoeffectKind.Embedded kind, CoeffectMode.None

let transl = 
  Translation.Flat.translate (Typed((), Expr.Builtin("finput", []))) [] typed 
  |> Translation.contract
  |> TypeChecker.typeCheck builtins2 kind2 mode2

open Coeffects.Evaluation

let args = 
  [ Value.Tuple [ Value.ListComonad [ Value.Number(1000.0) ]]
    Value.Tuple [ Value.ListComonad [ Value.Number(1.0); Value.Number(2.0) ]] ]
let sinput = Value.Tuple []

match eval { Kind = kind; Mode = mode; Variables = Map.ofSeq ["sinput", sinput] } transl with
| Value.Functions f -> f args
| _ -> failwith "Expected function"

(*
let typ (Typed((_, t), _)) = t

let rec check ctx (Typed((), e)) : Typed<CoeffVars * Type> * ResultContext = 
  match e with
  | Expr.Var(name) ->
      let typ = 
        match ctx.Variables.TryFind name with
        | Some typ -> typ
        | None -> failwith ("Variable '" + name + "' not in scope.")
      Typed((CoeffVars.var name Coeffect.Use typ, typ), Expr.Var name), Result.empty


  | Expr.Fun(TypedPat(_, Pattern.Var v) as pat, body) ->
      // Type check body with context containing `v : 'newTypeVar` for each new variable
      // let typedPat, ctxBody = checkPattern ctx pat
      let varTyp = Type.Variable(ctx.NewTypeVar())
      let ctxBody = Context.addVar v varTyp ctx
      let typedPat = TypedPat((CoeffVars.empty, varTyp), Pattern.Var v)

      let body, cbody = check ctxBody body      
      let (varCoeff, varTyp), cvs = CoeffVars.remove v (cvars body)

      // Return type is `varTyp -{ s }-> typOfBody` with context annotated with `r`
      Typed((cvs, Type.Func(varCoeff, varTyp, typ body)), Expr.Fun(typedPat, body)), cbody

  | Expr.App(l, r) ->
      let el, cl = check ctx l
      let er, cr = check ctx r
      // Generate type constraint for `typ el = typ er -{ t }-> newTypVar`
      let tout = Type.Variable(ctx.NewTypeVar())
      let cvar = Coeffect.Variable(ctx.NewCoeffectVar())
      let res = Result.merge cl cr |> Result.constrainTypes [ typ el, Type.Func(cvar, typ er, tout) ]
      // Resulting coeffect is `r + (s * t)` where r = coeff el and s = coeff er
      //let c = Coeffect.Split(coeff el, Coeffect.Seq(cvar, coeff er))
      let cvs = CoeffVars.merge (cvars el) (cvars er |> CoeffVars.mapCoeff (fun c -> Coeffect.Seq(cvar, c)))
      Typed((cvs, tout), Expr.App(el, er)), res

  | Expr.Binary(op, l, r) ->
      let el, cl = check ctx l
      let er, cr = check ctx r
      let cc = [ typ el, Type.Primitive "num"; typ er, Type.Primitive "num" ]
      let res = Result.merge cl cr |> Result.constrainTypes cc
      //let c = Coeffect.Split(coeff el, coeff er)
      let cvs = CoeffVars.merge (cvars el) (cvars er)
      Typed((cvs, Type.Primitive "num"), Expr.Binary(op, el, er)), res


let annotated, ctx = check (Context.empty  (fun _ _ -> failwith "?") CoeffectKind.PastValues) expr
let solved, cequals = solve ctx.TypeConstraints Map.empty []

let normalizeCoeffect c = c

annotated |> Expr.mapType (fun (cs, t) -> 
  cs |> Map.map (fun _ (c, t) -> normalizeType normalizeCoeffect solved t),
  normalizeType normalizeCoeffect solved t)

//let typed = TypeChecker.typeCheck (fun _ _ -> failwith "!") CoeffectKind.PastValues expr


(*
let translation () =
  let source = """
let h = prev (fun y -> 
  (fun x -> 1 + prev x) (prev y))
in h 42"""

  //let source = "let ?x = 1 in ?x"  
  let (Parsec.Parser lex) = Lexer.lexer
  let tokens = lex (List.ofArray (source.ToCharArray())) |> Option.get |> snd
  let tokens' = tokens |> List.filter (function Token.White _ -> false | _ -> true)
  let (Parsec.Parser pars) = Parser.expr ()
  let expr = pars tokens' |> Option.get |> snd
  let typed = TypeChecker.typeCheck (fun _ _ -> failwith "!") CoeffectKind.PastValues expr
      
  let transle  = 
    translate (Typed((), Expr.Builtin("input", []))) [] typed 
    |> contract
    //|> Expr.mapType (fun () -> Map.empty, Coeffect.Ignore, Type.Func(Coeffect.Ignore, Type.Primitive "!", Type.Primitive "!"))
    |> typeCheck (builtins (coeff typed)) (CoeffectKind.Embedded CoeffectKind.PastValues)

  let annotated, ctx = check (Context.empty (builtins (coeff typed)) CoeffectKind.ImplicitParams) transle
  let solved, cequals = solve ctx.TypeConstraints Map.empty []

  [ for c1, c2 in cequals do
      match c1, c2 with
      | Coeffect.Variable v, Coeffect.Closed o
      | Coeffect.Closed o, Coeffect.Variable v -> yield v, o
      | l, r when ImplicitParams.evalCoeffect Map.empty l = ImplicitParams.evalCoeffect Map.empty r -> ()
      | _ -> failwith "Cannot resolve constraint." ]
  |> ignore
      
  let normalizeCoeffect = 
    match kind with
    | CoeffectKind.ImplicitParams -> 
        // Solve coeffects & reduce to normalized form `p1 + .. + pn` 
        let csolved = ImplicitParams.solve (ctx.CoeffectConstraints @ cequals)
        let rec normalizeImplicits c = 
          ImplicitParams.evalCoeffect csolved c |> Seq.fold (fun c p -> 
            let t = normalizeType normalizeImplicits solved (ctx.ImplicitTypes.[p])
            Coeffect.Split(c, Coeffect.ImplicitParam(p, t))) Coeffect.Use
        normalizeImplicits

    | CoeffectKind.PastValues -> 
        // Solve coeffects & reduce to normalized form `n` 
        let psolved = Dataflow.solve (ctx.CoeffectConstraints @ cequals)
        let normalizePast c = Coeffect.Past(Dataflow.evalCoeffect psolved c)
        normalizePast

  // Replace all type & coeffect variables with solved version
  annotated |> Expr.mapType (fun (v, c, t) -> 
    v |> Map.map (fun _ t -> normalizeType normalizeCoeffect solved t),
    normalizeCoeffect c, 
    normalizeType normalizeCoeffect solved t)

  ()

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
*)*)