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
    CoeffectMode : CoeffectMode
    NewTypeVar : unit -> string 
    NewCoeffectVar : unit -> string
    ImplicitParams : Map<string, Type> }

/// Context that is propagated from leafs to botttom (collects constraints)
type ResultContext = 
  { TypeConstraints : list<Type * Type> 
    CoeffectConstraints : list<Coeffect * Coeffect>
    ImplicitTypes : Map<string, Type> 
    UsedVariables : Set<string> }


// ------------------------------------------------------------------------------------------------
// Helper functions for the context types above
// ------------------------------------------------------------------------------------------------

/// Helper functions for adding things to the input context
module Context = 
  let empty builtins kind mode =
    let lastTyp = ref 0
    let lastCoef = ref 0
    let newTyVar = fun () -> incr lastTyp; string lastTyp.Value 
    { Variables = Map.empty
      CoeffectKind = kind
      CoeffectMode = mode
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
  let empty vs = 
    { TypeConstraints = []; CoeffectConstraints = []; 
      ImplicitTypes = Map.empty; UsedVariables = Set.ofList vs }
  
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
      CoeffectConstraints = rc1.CoeffectConstraints @ rc2.CoeffectConstraints 
      UsedVariables = Set.union rc1.UsedVariables rc2.UsedVariables }
  let addImplicit name t rc = 
    { rc with ImplicitTypes = rc.ImplicitTypes.Add(name, t) }
  let constrainTypes constr rc = 
    { rc with TypeConstraints = rc.TypeConstraints @ constr }
  let constrainCoeffects constr rc = 
    { rc with CoeffectConstraints = rc.CoeffectConstraints @ constr }
  let removeVars vs rc = 
    { rc with UsedVariables = rc.UsedVariables - set vs }

/// Helper functions for structural coeffects. The only interesting one is `merge`, 
/// which implements 'contraction' (and joins variables from multiple contexts)
module Structural = 
  let addVar v c t vs = Map.add v (c, t) vs
  let ofVars c vs = vs |> Map.map (fun _ t -> c, t)
  let remove v c = 
    match Map.tryFind v c with
    | Some r -> fst r, Map.remove v c
    | None -> Coeffect.Ignore, c
  let mapCoeff f c = c |> Map.map (fun k (c, t) -> f c, t)
  let empty = Map.empty
  let merge c1 c2 = 
    let shared = 
      Set.intersect
        (c1 |> Map.toList |> List.map fst |> set)
        (c2 |> Map.toList |> List.map fst |> set) 
    [ for k, v in Map.toList c1 do
        if not (shared.Contains k) then yield k, v
      for k, v in Map.toList c2 do
        if not (shared.Contains k) then yield k, v
      for k in Set.toList shared do
        let (c1, t), (c2, _) = c1.[k], c2.[k]
        yield k, (Coeffect.Split(c1, c2), t) ] |> Map.ofSeq   


/// Helper that returns the type of a typed expression
let typ (Typed((_, _, t), _)) = t
/// Helper that returns the coeffect of a typed expression
let coeff (Typed((_, c, _), _)) = c
/// Helper that returns the structural coeffect vector of a typed expression
let cvars (Typed((c, _, _), _)) = c

/// Helper that returns the type of a typed expression
let ptyp (TypedPat((_, _, t), _)) = t
/// Creates type information containing just the type (for use in patterns)
let justTyp t = Structural.empty, Coeffect.Ignore, t

/// Workaround for a FunScript bug
let unzip l = List.foldBack (fun (x,y) (xs,ys) -> x::xs, y::ys) l ([], [])


// ------------------------------------------------------------------------------------------------
// Type checking: Takes an untyped expression and returns a typed expression annotated with 
// structural coeffect (CoeffVars), flat coeffect (Coeffect) and the type.
//    InputContext -> Typed<unit> -> Typed<CoeffVars * Coeffect * Type> * ResultContext
// ------------------------------------------------------------------------------------------------

/// Type checks a pattern & adds bound variables to the context 
let rec checkPattern ctx (TypedPat((), pat)) = 
  match pat with 
  | Pattern.Var v ->
      let varTyp = Type.Variable(ctx.NewTypeVar())
      let ctx = Context.addVar v varTyp ctx
      TypedPat(justTyp varTyp, Pattern.Var v), ctx, [v]

  | Pattern.Tuple pats ->
      let typedPats, ctx, vars = pats |> List.fold (fun (typedPats, ctx, vars1) pat -> 
        let typedPat, ctx, vars2 = checkPattern ctx pat
        typedPat::typedPats, ctx, vars1 @ vars2) ([], ctx, [])
      let typedPats = List.rev typedPats
      TypedPat(justTyp (Type.Tuple(List.map ptyp typedPats)), Pattern.Tuple(typedPats)), ctx, vars

  | Pattern.QVar _ ->
      failwith "The ?v pattern is allowed only in let bindings."

/// The type checking function that reconstructs types and collects type & coeffect constraints
let rec check ctx (Typed((), e)) : Typed<CoeffVars * Coeffect * Type> * ResultContext = 

  // Returns the result of 'check' - when the kind is 'Embedded', meaning that we
  // do not care about coeffects, we also replace all coeffects with 'None'
  let typed (allVars:CoeffVars) (coeff:Coeffect) (typ:Type) e res = 
    let usedVars = 
      if ctx.CoeffectMode <> CoeffectMode.Structural then allVars
      else allVars |> Map.filter (fun k _ -> res.UsedVariables.Contains k)
    match ctx.CoeffectKind, ctx.CoeffectMode with 
    | CoeffectKind.Embedded _, _ -> 
        Typed((Structural.mapCoeff (fun _ -> Coeffect.None) usedVars, Coeffect.None, typ), e), res
    | _, CoeffectMode.Flat -> 
        let typ = match typ with Type.Func((cflat, _), t1, t2) -> Type.Func((cflat, Coeffect.None), t1, t2) | _ -> typ
        Typed((Structural.mapCoeff (fun _ -> Coeffect.None) usedVars, coeff, typ), e), res
    | _, CoeffectMode.Structural -> 
        let typ = match typ with Type.Func((_, cstruct), t1, t2) -> Type.Func((Coeffect.None, cstruct), t1, t2) | _ -> typ
        Typed((usedVars, Coeffect.None, typ), e), res
    | _ -> Typed((usedVars, coeff, typ), e), res


  // IMPLICIT PARAMETERS
  match e with 
  | Expr.Let(TypedPat((), Pattern.QVar qv), arg, body) ->
      if ctx.CoeffectKind <> CoeffectKind.ImplicitParams then   
        failwith "Implicit parameter binding in another expression"

      // Add coeffect constraint `{ ?qv } + coeffVar = coeff body` and use
      // `coeffVar + (coeffVar * coeff arg)` as the coeffect of the let binding
      let earg, carg = check ctx arg
      let ebody, cbody = check (Context.addImplicit qv (typ earg) ctx) body
      let cvar = Coeffect.Variable(ctx.NewCoeffectVar())
      let cconstrs = [ Coeffect.Split(Coeffect.ImplicitParam(qv, typ earg), cvar), coeff ebody ]
      
      // This would be more akin to typing of 'let' but the below matches the translation
      // let cflat = Coeffect.Split(cvar, Coeffect.Seq(cvar, coeff earg))
      let cflat = Coeffect.Split(cvar, coeff earg) 
      let cstruct = Structural.ofVars Coeffect.Ignore ctx.Variables
      let res = Result.merge carg cbody |> Result.constrainCoeffects cconstrs
      typed cstruct cflat (typ ebody) (Expr.Let(TypedPat(justTyp (typ earg), Pattern.QVar qv), earg, ebody)) res

  | Expr.QVar(name) ->
      if ctx.CoeffectKind <> CoeffectKind.ImplicitParams then 
        failwith "Implicit parameter access in another expression"
      let typ = 
        match ctx.Variables.TryFind name with 
        | Some typ -> typ
        | None -> Type.Variable(ctx.NewTypeVar())
      let cflat = Coeffect.ImplicitParam(name, typ)
      let cstruct = Structural.ofVars Coeffect.Ignore ctx.Variables
      let res = Result.addImplicit name typ (Result.empty [])
      typed cstruct cflat typ (Expr.QVar name) res


  // DATAFLOW COMPUTATIONS
  | Expr.Prev(e) ->
      if ctx.CoeffectKind <> CoeffectKind.PastValues then 
        failwith "Prev keyword in another expression"
      let ebody, res = check ctx e
      let cflat = Coeffect.Seq(Coeffect.Past 1, coeff ebody)
      let cstruct = cvars ebody |> Structural.mapCoeff (fun c -> Coeffect.Seq(Coeffect.Past 1, c))
      typed cstruct cflat (typ ebody) (Expr.Prev ebody) res


  // CORE EXPRESSIONS (VAR, CONST, APP, ABS)
  | Expr.Var(name) ->
      let typ = 
        match ctx.Variables.TryFind name with
        | Some typ -> typ
        | None -> failwith ("Variable '" + name + "' not in scope.")
      let cflat = Coeffect.Use
      let cstruct = 
        Structural.ofVars Coeffect.Ignore ctx.Variables 
        |> Structural.addVar name Coeffect.Use typ
      typed cstruct cflat typ (Expr.Var name) (Result.empty [name])

  | Expr.Integer(n) ->
      typed (Structural.ofVars Coeffect.Ignore ctx.Variables) 
        Coeffect.Ignore (Type.Primitive "int") (Expr.Integer n) (Result.empty [])

  | Expr.Fun(pat, body) ->
      // Type check body with context containing `v : 'newTypeVar` for each new variable
      let typedPat, ctxBody, vars = checkPattern ctx pat
      let body, cbody = check ctxBody body      

      // Generate coeffect variables `r ^ s` and constrain `r ^ s = bodyCoeffect`
      // and also `r = c1 + .. + cn where ci \in implicitParamsInScope`
      let cflat = Coeffect.Variable(ctxBody.NewCoeffectVar())
      let cflatFun = Coeffect.Variable(ctxBody.NewCoeffectVar())
      let constrs = 
        if ctx.CoeffectKind = CoeffectKind.ImplicitParams then
          // When type-checking implicit params, constrain the implicit parameters on the
          // declaration side to those that are currently in lexical scope
          let inScope = ctxBody.ImplicitParams |> Map.toList |> List.fold (fun s (c, t) -> 
            Coeffect.Split(s, Coeffect.ImplicitParam(c, t))) Coeffect.Ignore
          [ cflat, inScope ]
        else []
      let cbody = 
        cbody 
        |> Result.constrainCoeffects ([Coeffect.Merge(cflat, cflatFun), coeff body ] @ constrs)
        |> Result.removeVars vars
      
      // Extract the coeffect of the boud variable and remove it 
      // (and fail if the pattern is more complicated and we're doing structural coeffects)
      let cstructFun, cstruct = 
        match pat with 
        | TypedPat((), Pattern.Var v) -> Structural.remove v (cvars body)
        | _ -> 
          if (ctx.CoeffectMode &&& CoeffectMode.Structural) = CoeffectMode.Structural then 
            failwith "Structural langauge supports only simple patterns"
          else Coeffect.None, Structural.ofVars Coeffect.None ctx.Variables

      // Annotate the function type with both flat & structural coeffect
      typed cstruct cflat (Type.Func((cflatFun, cstructFun), ptyp typedPat, typ body)) 
        (Expr.Fun(typedPat, body)) cbody

  | Expr.App(l, r) ->
      // Generate type constraint for `typ el = typ er -{ cflat, cstruct }-> newTypVar`
      let el, cl = check ctx l
      let er, cr = check ctx r
      let tout = Type.Variable(ctx.NewTypeVar())
      let cflatVar = Coeffect.Variable(ctx.NewCoeffectVar())
      let cstructVar = Coeffect.Variable(ctx.NewCoeffectVar())
      let ftyp = 
          match ctx.CoeffectMode with
          | CoeffectMode.Flat -> Type.Func((cflatVar, Coeffect.None), typ er, tout)
          | CoeffectMode.Structural -> Type.Func((Coeffect.None, cstructVar), typ er, tout)
          | _ -> Type.Func((cflatVar, cstructVar), typ er, tout)
      let res = Result.merge cl cr |> Result.constrainTypes [ typ el, ftyp ]

      // Resulting coeffect is `r + (s * t)` where r = coeff el and s = coeff er
      let cflat = Coeffect.Split(coeff el, Coeffect.Seq(cflatVar, coeff er))
      let cstruct = Structural.merge (cvars el) (cvars er |> Structural.mapCoeff (fun c -> Coeffect.Seq(cstructVar, c)))
      typed cstruct cflat tout (Expr.App(el, er)) res


  // DERIVED AND OTHER EXPRESSIONS (BUILTINS, TUPLES)
  | Expr.Let(pat, arg, body) ->
      let earg, carg = check ctx arg
      let typedPat, newCtx, vars = checkPattern ctx pat
      let ebody, cbody = check newCtx body
      let res = 
        Result.merge carg cbody 
        |> Result.constrainTypes [ typ earg, ptyp typedPat ]
        |> Result.removeVars vars

      let cflat = Coeffect.Split(coeff ebody, Coeffect.Seq(coeff ebody, coeff earg))
      let cstruct = 
        match pat with
        | TypedPat((), Pattern.Var name) ->
            let carg, cstruct = Structural.remove name (cvars ebody)
            Structural.merge cstruct
              (cvars earg |> Structural.mapCoeff (fun c -> Coeffect.Seq(c, carg)))
        | _ ->
          if (ctx.CoeffectMode &&& CoeffectMode.Structural) = CoeffectMode.Structural then 
            failwith "Structural langauge supports only simple patterns"
          else Structural.ofVars Coeffect.None ctx.Variables

      typed cstruct cflat (typ ebody) (Expr.Let(typedPat, earg, ebody)) res

  | Expr.Builtin(name, cl) -> 
      let t = ctx.BuiltinTypings ctx (name, cl)
      let cflat = Coeffect.Ignore
      let cstruct = Structural.ofVars Coeffect.Ignore ctx.Variables
      typed cstruct cflat t (Expr.Builtin(name, cl)) (Result.empty [])

  | Expr.Tuple(args) ->
      let eargs, ress = List.map (check ctx) args |> unzip
      let res = List.reduce Result.merge ress
      let cflat = eargs |> List.map coeff |> List.reduce (fun c1 c2 -> Coeffect.Split(c1, c2))
      let cstruct = eargs |> List.map cvars |> List.reduce Structural.merge
      typed cstruct cflat (Type.Tuple(List.map typ eargs)) (Expr.Tuple(eargs)) res

  | Expr.Binary(op, l, r) ->
      let el, cl = check ctx l
      let er, cr = check ctx r
      let cc = [ typ el, Type.Primitive "int"; typ er, Type.Primitive "int" ]
      let res = Result.merge cl cr |> Result.constrainTypes cc
      let cflat = Coeffect.Split(coeff el, coeff er)
      let cstruct = Structural.merge (cvars el) (cvars er)
      typed cstruct cflat (Type.Primitive "int") (Expr.Binary(op, el, er)) res

           
// ------------------------------------------------------------------------------------------------
// Entry point - run the type checker & solve the constraints
// ------------------------------------------------------------------------------------------------

let typeCheck builtins kind mode expr : Typed<CoeffVars * Coeffect * Type> =
  let annotated, ctx = check (Context.empty builtins kind mode) expr
  let solved, cequals = solve ctx.TypeConstraints Map.empty []
    
  // for l, r in cequals do printfn "\n  %A\n= %A" l r
  let normalizeCoeffect = 
    match kind with
    | CoeffectKind.Embedded c ->
        let equal c1 c2 = 
          match c with
          | CoeffectKind.ImplicitParams -> ImplicitParams.evalCoeffect Map.empty c1 = ImplicitParams.evalCoeffect Map.empty c2
          | CoeffectKind.PastValues -> Dataflow.evalCoeffect Map.empty c1 = Dataflow.evalCoeffect Map.empty c2
          | _ -> failwith "Wrong embedded coeffect"

        let solved = 
          [ for c1, c2 in cequals do
              match c1, c2 with
              | Coeffect.None, _ | _, Coeffect.None -> ()
              | Coeffect.Variable v, Coeffect.Closed o
              | Coeffect.Closed o, Coeffect.Variable v -> yield v, o
              | l, r when equal l r -> ()
              | _ -> failwith "Cannot resolve constraint." ] |> Map.ofSeq
              //| l, r -> failwithf "Cannot resolve constraint\n  %A\n= %A" l r ] |> Map.ofSeq
        let normalizeNone c = 
          match c with 
          | Coeffect.None -> Coeffect.None
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
          match c with 
          | Coeffect.None -> Coeffect.None
          | c ->
              ImplicitParams.evalCoeffect csolved c |> Seq.fold (fun c p -> 
                let t = normalizeType normalizeImplicits solved (ctx.ImplicitTypes.[p])
                Coeffect.Split(c, Coeffect.ImplicitParam(p, t))) Coeffect.Use
        normalizeImplicits

    | CoeffectKind.PastValues -> 
        // Solve coeffects & reduce to normalized form `n` 
        let psolved = Dataflow.solve (ctx.CoeffectConstraints @ cequals)
        let normalizePast c = 
          match c with 
          | Coeffect.None -> Coeffect.None
          | c -> Coeffect.Past(Dataflow.evalCoeffect psolved c)
        normalizePast

  // Replace all type & coeffect variables with solved version
  annotated |> Expr.mapType (fun (v, c, t) -> 
    v |> Map.map (fun _ (c, t) -> normalizeCoeffect c, normalizeType normalizeCoeffect solved t),
    normalizeCoeffect c, 
    normalizeType normalizeCoeffect solved t)