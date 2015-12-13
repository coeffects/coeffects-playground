// ------------------------------------------------------------------------------------------------
// Type checker for a mini-ML langauge - returns typed expression with generated constraints
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.TypeChecker
open Coeffects
open Coeffects.Ast
open Coeffects.Solver

/// Context that is propagated from the bottom to the leafs in type checking
type InputContext = 
  { Variables : Map<string, Type> 
    NewTypeVar : unit -> string 
    NewCoeffectVar : unit -> string
    ImplicitParams : Map<string, Type> }

/// Context that is propagated from leafs to botttom (collects constraints)
type ResultContext = 
  { TypeConstraints : list<Type * Type> 
    CoeffectConstraints : list<Coeffect * Coeffect>
    ImplicitTypes : Map<string, Type> }

/// Helper functions for adding things to the input context
module Context = 
  let empty() =
    let lastTyp = ref 0
    let lastCoef = ref 0
    { Variables = Map.empty
      NewCoeffectVar = fun () -> incr lastCoef; string lastCoef.Value 
      NewTypeVar = fun () -> incr lastTyp; string lastTyp.Value 
      ImplicitParams = Map.empty }
  let addVar name typ ctx = 
    { ctx with Variables = ctx.Variables.Add(name, typ) }
  let addImplicit name typ ctx = 
    { ctx with ImplicitParams = ctx.ImplicitParams.Add(name, typ) }

/// Helper functions for adding things to the result context
module Result = 
  let empty = 
    { TypeConstraints = []; CoeffectConstraints = []; ImplicitTypes = Map.empty }

  let merge rc1 rc2 = 
    // If an implicit parameter appears in both of the contexts, we 
    // generate new type equality constraint for their types
    let shared = 
      Set.intersect
        (rc1.ImplicitTypes |> Map.toList |> List.map fst |> set)
        (rc2.ImplicitTypes |> Map.toList |> List.map fst |> set) |> Set.toList
    let implConstraints = 
      shared |> List.map (fun k -> rc1.ImplicitTypes.[k], rc2.ImplicitTypes.[k])
    let newImplicits = 
      rc1.ImplicitTypes |> Map.toList |> List.fold (fun st (k, v) -> Map.add k v st) rc2.ImplicitTypes
    { TypeConstraints = rc1.TypeConstraints @ rc2.TypeConstraints @ implConstraints
      ImplicitTypes = newImplicits
      CoeffectConstraints = rc1.CoeffectConstraints @ rc2.CoeffectConstraints }

  let addImplicit name t rc = 
    { rc with ImplicitTypes = rc.ImplicitTypes.Add(name, t) }
  let constrainTypes constr rc = 
    { rc with TypeConstraints = rc.TypeConstraints @ constr }
  let constrainCoeffects constr rc = 
    { rc with CoeffectConstraints = rc.CoeffectConstraints @ constr }

/// Helper that returns the type of a typed expression
let typ (Typed.Typed((_, t), _)) = t
/// Helper that returns the coeffect of a typed expression
let coeff (Typed.Typed((c, _), _)) = c


// ------------------------------------------------------------------------------------------------
// Type checking: InputContext -> Typed<unit> -> Typed<Coeffect * Type> * ResultContext
// ------------------------------------------------------------------------------------------------


/// The type checking function that reconstructs types and collects type & coeffect constraints
let rec check ctx (Typed.Typed((), e)) : Typed<Coeffect * Type> * ResultContext = 
  match e with 
  | Expr.Var(name) ->
      let typ = 
        match ctx.Variables.TryFind name with
        | Some typ -> typ
        | None -> failwith ("Variable '" + name + "' not in scope.")
      Typed.Typed((Coeffect.Use, typ), Expr.Var name), Result.empty

  | Expr.QVar(name) ->
      let typ = 
        match ctx.Variables.TryFind name with 
        | Some typ -> typ
        | None -> Type.Variable(ctx.NewTypeVar())
      let res = Result.addImplicit name typ Result.empty
      Typed.Typed((Coeffect.ImplicitParam(name, typ), typ), Expr.QVar name), res

  | Expr.Integer(n) ->
      Typed.Typed((Coeffect.Ignore, Type.Primitive "int"), Expr.Integer n), Result.empty

  | Expr.Binary(op, l, r) ->
      let el, cl = check ctx l
      let er, cr = check ctx r
      let cc = [ typ el, Type.Primitive "int"; typ er, Type.Primitive "int" ]
      let res = Result.merge cl cr |> Result.constrainTypes cc
      let c = Coeffect.Split(coeff el, coeff er)
      Typed.Typed((c, Type.Primitive "int"), Expr.Binary(op, el, er)), res

  | Expr.Fun(Pattern.QVar v, body) ->
      failwith "The ?v pattern is allowed only in let bindings, not in functions."

  | Expr.Fun(Pattern.Var v, body) ->
      // Type check body with context containing `v : 'newTypeVar`
      let varTyp = Type.Variable(ctx.NewTypeVar())
      let ctx = Context.addVar v varTyp ctx
      let body, cbody = check ctx body      
      // Generate coeffect variables `r ^ s` and constrain `r ^ s = bodyCoeffect`
      // and also `r = c1 + .. + cn where ci \in implicitParamsInScope`
      let cvar1 = Coeffect.Variable(ctx.NewCoeffectVar())
      let cvar2 = Coeffect.Variable(ctx.NewCoeffectVar())
      let inScope = ctx.ImplicitParams |> Map.toList |> List.fold (fun s (c, t) -> 
        Coeffect.Split(s, Coeffect.ImplicitParam(c, t))) Coeffect.Ignore
      let cbody = cbody |> Result.constrainCoeffects [Coeffect.Merge(cvar1, cvar2), coeff body; cvar1, inScope ] 
      // Return type is `varTyp -{ s }-> typOfBody` with context annotated with `r`
      Typed.Typed((cvar1, Type.Func(cvar2, varTyp, typ body)), Expr.Fun(Pattern.Var v, body)), cbody

  | Expr.App(l, r) ->
      let el, cl = check ctx l
      let er, cr = check ctx r
      // Generate type constraint for `typ el = typ er -{ t }-> newTypVar`
      let tout = Type.Variable(ctx.NewTypeVar())
      let cvar = Coeffect.Variable(ctx.NewCoeffectVar())
      let res = Result.merge cl cr |> Result.constrainTypes [ typ el, Type.Func(cvar, typ er, tout) ]
      // Resulting coeffect is `r + (s * t)` where r = coeff el and s = coeff er
      let c = Coeffect.Split(coeff el, Coeffect.Seq(cvar, coeff er))
      Typed.Typed((c, tout), Expr.App(el, er)), res

  | Expr.Let(Pattern.Var v, arg, body) ->
      let earg, carg = check ctx arg
      let ctx = Context.addVar v (typ earg) ctx
      let ebody, cbody = check ctx body
      let res = Result.merge carg cbody 
      let c = Coeffect.Split(coeff ebody, Coeffect.Seq(coeff ebody, coeff earg))
      Typed.Typed((c, typ ebody), Expr.Let(Pattern.Var v, earg, ebody)), res

  | Expr.Let(Pattern.QVar qv, arg, body) ->
      let earg, carg = check ctx arg
      // Add implicit parameter to the scope
      let ebody, cbody = check (Context.addImplicit qv (typ earg) ctx) body
      // Add coeffect constraint ` { ?qv } + coeffVar = coeff body` and use
      // `coeffVar + (coeffVar * coeff arg)` as the coeffect of the let binding
      let cvar = Coeffect.Variable(ctx.NewCoeffectVar())
      let cconstrs = [ Coeffect.Split(Coeffect.ImplicitParam(qv, typ earg), cvar), coeff ebody ]
      let c = Coeffect.Split(cvar, Coeffect.Seq(cvar, coeff earg))
      let res = Result.merge carg cbody |> Result.constrainCoeffects cconstrs
      Typed.Typed((c, typ ebody), Expr.Let(Pattern.QVar qv, earg, ebody)), res
       
// ------------------------------------------------------------------------------------------------
// Entry point - run the type checker & solve the constraints
// ------------------------------------------------------------------------------------------------

let typeCheck expr =
  let annotated, ctx = check (Context.empty ()) expr
  let solved, cequals = solve ctx.TypeConstraints Map.empty []
  let csolved = solveImplicits (ctx.CoeffectConstraints @ cequals)

  // Evaluate implicit parameters & generate `p1 + .. + pn` normalized form
  let rec evalSplits c = 
    evalCoeffect csolved c |> Seq.fold (fun c p -> 
      let t = normalize evalSplits solved (ctx.ImplicitTypes.[p])
      Coeffect.Split(c, Coeffect.ImplicitParam(p, t))) Coeffect.Ignore

  // Replace all type & coeffect variables with solved version
  annotated |> Expr.mapType (fun (c, t) -> 
    evalSplits c, 
    normalize evalSplits solved t)

(*
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

  let (Parsec.Parser lex) = Lexer.lexer
  let tokens = lex (List.ofArray (source().ToCharArray())) |> Option.get |> snd
  let tokens' = tokens |> List.filter (function Token.White _ -> false | _ -> true)
  let (Parsec.Parser pars) = Parser.expr ()
  let expr = pars tokens' |> Option.get |> snd
  let tt, ct = check (Context.empty ()) expr
  let solved, cequals = solve ct.TypeConstraints Map.empty []
  let csolved = solveImplicits (ct.CoeffectConstraints @ cequals)

  for c1, c2 in ct.CoeffectConstraints @ cequals do
    printfn "%A\n = %A\n" c1 c2 

  let rec evalSplits c = 
    evalCoeffect csolved c
    |> Seq.fold (fun c p -> 
        let t = normalize evalSplits solved (ct.ImplicitTypes.[p])
        Coeffect.Split(c, Coeffect.ImplicitParam(p, t))) Coeffect.Ignore
  
  tt |> Expr.mapType (fun (c, t) -> 
    evalCoeffect csolved c, 
    normalize evalSplits solved t)


  solveImplicits ct.CoeffectConstraints
//*)