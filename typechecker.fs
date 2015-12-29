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
  { BuiltinTypings : InputContext -> string * Coeffect list -> Type
    Variables : Vars
    CoeffectKind : CoeffectKind
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
  let empty builtins kind =
    let lastTyp = ref 0
    let lastCoef = ref 0
    let newTyVar = fun () -> incr lastTyp; string lastTyp.Value 
    { Variables = Map.empty
      CoeffectKind = kind
      NewCoeffectVar = fun () -> incr lastCoef; string lastCoef.Value 
      NewTypeVar = newTyVar
      BuiltinTypings = builtins 
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
let typ (Typed((_, _, t), _)) = t
/// Helper that returns the type of a typed expression
let ptyp (TypedPat((_, _, t), _)) = t
/// Helper that returns the coeffect of a typed expression
let coeff (Typed((_, c, _), _)) = c
/// Creates type information containing just the type (for use in patterns)
let justTyp t = Map.empty, Coeffect.Ignore, t
/// Workaround for a FunScript bug
let unzip l = List.foldBack (fun (x,y) (xs,ys) -> x::xs, y::ys) l ([], [])

// ------------------------------------------------------------------------------------------------
// Type checking: InputContext -> Typed<unit> -> Typed<Vars * Coeffect * Type> * ResultContext
// ------------------------------------------------------------------------------------------------

/// Type checks a pattern & adds bound variables to the context 
let rec checkPattern ctx (TypedPat((), pat))= 
  match pat with 
  | Pattern.Var v ->
      let varTyp = Type.Variable(ctx.NewTypeVar())
      let ctx = Context.addVar v varTyp ctx
      TypedPat(justTyp varTyp, Pattern.Var v), ctx

  | Pattern.Tuple pats ->
      let typedPats, ctx = pats |> List.fold (fun (typedPats, ctx) pat -> 
        let typedPat, ctx = checkPattern ctx pat
        typedPat::typedPats, ctx) ([], ctx)
      let typedPats = List.rev typedPats
      TypedPat(justTyp (Type.Tuple(List.map ptyp typedPats)), Pattern.Tuple(typedPats)), ctx

  | Pattern.QVar _ ->
      failwith "The ?v pattern is allowed only in let bindings."

/// The type checking function that reconstructs types and collects type & coeffect constraints
let rec check ctx (Typed((), e)) : Typed<Vars * Coeffect * Type> * ResultContext = 
  
  let returnCoeff c = 
    if ctx.CoeffectKind = CoeffectKind.None then Coeffect.None else c

  match e with 

  // Implicit parameters 

  | Expr.Let(TypedPat((), Pattern.QVar qv), arg, body) ->
      if ctx.CoeffectKind <> CoeffectKind.ImplicitParams then failwith "Implicit parameter binding in another expression"
      let earg, carg = check ctx arg
      // Add implicit parameter to the scope
      let ebody, cbody = check (Context.addImplicit qv (typ earg) ctx) body
      // Add coeffect constraint ` { ?qv } + coeffVar = coeff body` and use
      // `coeffVar + (coeffVar * coeff arg)` as the coeffect of the let binding
      let cvar = Coeffect.Variable(ctx.NewCoeffectVar())
      let cconstrs = [ Coeffect.Split(Coeffect.ImplicitParam(qv, typ earg), cvar), coeff ebody ]
      
      // let c = Coeffect.Split(cvar, Coeffect.Seq(cvar, coeff earg))
      let c = Coeffect.Split(cvar, coeff earg) // This is more sensible typing matching with the translation

      let res = Result.merge carg cbody |> Result.constrainCoeffects cconstrs
      Typed((ctx.Variables, c, typ ebody), Expr.Let(TypedPat(justTyp (typ earg), Pattern.QVar qv), earg, ebody)), res

  | Expr.QVar(name) ->
      if ctx.CoeffectKind <> CoeffectKind.ImplicitParams then failwith "Implicit parameter access in another expression"
      let typ = 
        match ctx.Variables.TryFind name with 
        | Some typ -> typ
        | None -> Type.Variable(ctx.NewTypeVar())
      let res = Result.addImplicit name typ Result.empty
      Typed((ctx.Variables, Coeffect.ImplicitParam(name, typ), typ), Expr.QVar name), res

  // Data-flow computations

  | Expr.Prev(e) ->
      if ctx.CoeffectKind <> CoeffectKind.PastValues then failwith "Prev keyword in another expression"
      let ebody, cbody = check ctx e
      let c = Coeffect.Seq(Coeffect.Past 1, coeff ebody)
      Typed((ctx.Variables, c, typ ebody), Expr.Prev(ebody)), cbody

  // Normal expressions of the language

  | Expr.Builtin(name, cl) -> 
      let t = ctx.BuiltinTypings ctx (name, cl)
      let c = Coeffect.Ignore
      Typed((ctx.Variables, returnCoeff c, t), Expr.Builtin(name, cl)), Result.empty

  | Expr.Tuple(args) ->
      let eargs, ress = List.map (check ctx) args |> unzip
      let res = List.reduce Result.merge ress
      let c = eargs |> List.map coeff |> List.reduce (fun c1 c2 -> Coeffect.Split(c1, c2))
      Typed((ctx.Variables, returnCoeff c, Type.Tuple(List.map typ eargs)), Expr.Tuple(eargs)), res

  | Expr.Var(name) ->
      let typ = 
        match ctx.Variables.TryFind name with
        | Some typ -> typ
        | None -> failwith ("Variable '" + name + "' not in scope.")
      let c =Coeffect.Use
      Typed((ctx.Variables, returnCoeff c, typ), Expr.Var name), Result.empty

  | Expr.Integer(n) ->
      let c = Coeffect.Ignore
      Typed((ctx.Variables, c, Type.Primitive "int"), Expr.Integer n), Result.empty

  | Expr.Binary(op, l, r) ->
      let el, cl = check ctx l
      let er, cr = check ctx r
      let cc = [ typ el, Type.Primitive "int"; typ er, Type.Primitive "int" ]
      let res = Result.merge cl cr |> Result.constrainTypes cc
      let c = Coeffect.Split(coeff el, coeff er)
      Typed((ctx.Variables, returnCoeff c, Type.Primitive "int"), Expr.Binary(op, el, er)), res

  | Expr.Fun(pat, body) ->
      // Type check body with context containing `v : 'newTypeVar` for each new variable
      let typedPat, ctx = checkPattern ctx pat
      let body, cbody = check ctx body      
      // Generate coeffect variables `r ^ s` and constrain `r ^ s = bodyCoeffect`
      // and also `r = c1 + .. + cn where ci \in implicitParamsInScope`
      let cvar1 = Coeffect.Variable(ctx.NewCoeffectVar())
      let cvar2 = Coeffect.Variable(ctx.NewCoeffectVar())
      let constrs = 
        if ctx.CoeffectKind = CoeffectKind.ImplicitParams then
          // When type-checking implicit params, constrain the implicit parameters on the
          // declaration side to those that are currently in lexical scope
          let inScope = ctx.ImplicitParams |> Map.toList |> List.fold (fun s (c, t) -> 
            Coeffect.Split(s, Coeffect.ImplicitParam(c, t))) Coeffect.Ignore
          [ cvar1, inScope ]
        else []
      let cbody = cbody |> Result.constrainCoeffects ([Coeffect.Merge(cvar1, cvar2), coeff body ] @ constrs)

      // Return type is `varTyp -{ s }-> typOfBody` with context annotated with `r`
      Typed((ctx.Variables, returnCoeff cvar1, Type.Func(cvar2, ptyp typedPat, typ body)), Expr.Fun(typedPat, body)), cbody

  | Expr.App(l, r) ->
      let el, cl = check ctx l
      let er, cr = check ctx r
      // Generate type constraint for `typ el = typ er -{ t }-> newTypVar`
      let tout = Type.Variable(ctx.NewTypeVar())
      let cvar = Coeffect.Variable(ctx.NewCoeffectVar())
      let res = Result.merge cl cr |> Result.constrainTypes [ typ el, Type.Func(cvar, typ er, tout) ]
      // Resulting coeffect is `r + (s * t)` where r = coeff el and s = coeff er
      let c = Coeffect.Split(coeff el, Coeffect.Seq(cvar, coeff er))
      Typed((ctx.Variables, returnCoeff c, tout), Expr.App(el, er)), res

  | Expr.Let(pat, arg, body) ->
      let earg, carg = check ctx arg
      let typedPat, ctx = checkPattern ctx pat
      let ebody, cbody = check ctx body
      let res = Result.merge carg cbody |> Result.constrainTypes [ typ earg, ptyp typedPat ]
      let c = Coeffect.Split(coeff ebody, Coeffect.Seq(coeff ebody, coeff earg))
      Typed((ctx.Variables, returnCoeff c, typ ebody), Expr.Let(typedPat, earg, ebody)), res
           
// ------------------------------------------------------------------------------------------------
// Entry point - run the type checker & solve the constraints
// ------------------------------------------------------------------------------------------------

let typeCheck builtins kind expr : Typed<Vars * Coeffect * Type> =
  let annotated, ctx = check (Context.empty builtins kind) expr
  let solved, cequals = solve ctx.TypeConstraints Map.empty []
    
  // for l, r in cequals do printfn "\n  %A\n= %A" l r
  let normalizeCoeffect = 
    match kind with
    | CoeffectKind.None ->
        let solved = 
          [ for c1, c2 in cequals do
              match c1, c2 with
              | Coeffect.Variable v, Coeffect.Closed o
              | Coeffect.Closed o, Coeffect.Variable v -> yield v, o
              | l, r when ImplicitParams.evalCoeffect Map.empty l = ImplicitParams.evalCoeffect Map.empty r -> ()
              | _ -> failwith "Cannot resolve constraint." ] |> Map.ofSeq
              //| l, r -> failwithf "Cannot resolve constraint\n  %A\n= %A" l r ] |> Map.ofSeq
        let normalizeNone c = 
          match c with 
          | Coeffect.Closed c -> c
          | Coeffect.Variable s when solved.ContainsKey s -> solved.[s]
          | Coeffect.Variable s -> Coeffect.None
          | c -> 
            failwith "Cannot normalize coeffect"
            //failwithf "Cannot normalize coeffect: %A" c
        normalizeNone

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