// ------------------------------------------------------------------------------------------------
// Coeffect translation that translates source language to a target language with comonads
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Translation
open Coeffects
open Coeffects.Ast

// Helpers for constructing unit-typed expressions
let (!) e = Typed((), e)
let (!!) p = TypedPat((), p)
let (|@|) a b = !Expr.App(a, b)

// Helpers for accessing coeffects/variables from typed expressions
let cvars (Typed((c, _, _), _)) : CoeffVars = c
let coeff (Typed((_, c, _), _)) = c
let typ (Typed((_, _, t), _)) = t

// Helpers for creating coeffect annotations
let ( ^^ ) l r = Coeffect.Merge(l, r)
let ( ++ ) l r = Coeffect.Split(l, r)
let ( ** ) l r = Coeffect.Seq(l, r)

/// Drops the specified implicit parameter from a coeffect annotation
let rec removeImplicit (v, vt) coeff = 
  match coeff with
  | Coeffect.Split(nested, Coeffect.ImplicitParam(n, nt)) when n = v -> 
      nested
  | Coeffect.Split(nested, Coeffect.ImplicitParam(n, nt)) -> 
      Coeffect.Split(removeImplicit (v, vt) nested, Coeffect.ImplicitParam(n, nt))
  | Coeffect.Use -> Coeffect.Use
  | _ -> failwith "Unexpected coeffect shape."


// ------------------------------------------------------------------------------------------------
// Translation for flat coeffects
// ------------------------------------------------------------------------------------------------

module Flat = 
  /// Create a builtin primitive with flat coeffect annotation
  let builtin (s, ans) = Expr.Builtin(s, [ for a in ans -> Annotation.Flat(a)])

  /// Translate function tyopes: `t1 -{ r }-> t2`  to `C {r} t1 -> t2`
  let rec translateType t = 
    match t with 
    | Type.Variable _
    | Type.Primitive _ -> t
    | Type.Func((cf, _), t1, t2) -> 
        Type.Func((Coeffect.None, Coeffect.None), Type.FlatComonad(cf, translateType t1), translateType t2)
    | Type.Tuple ts -> Type.Tuple(List.map translateType ts)
    | Type.FlatComonad _ 
    | Type.StructuralComonad _ -> Errors.unexpected "Comonad type appears in the source program."


  /// Implements the flat coeffect translation. Takes a fresh name generator for
  /// naming 'ctx' variables, expression representing the current context and a
  /// list of variables in the 'ctx' environment.
  let rec translate freshName ctx vars (Typed((v,c,t), e)) = 
    let translate = translate freshName 
    match e with
    // CORE EXPRESSIONS (VAR, CONST, APP, ABS)
    | Expr.Number(n) ->
        !Expr.Number(n)

    | Expr.Var(v) ->
        // The context stores variables in a tuple with unit at the end, e.g. (v1, (v2, (v3, ()))
        // so we generate something like: `fst (snd (.... (snd ctx)))`
        let rec getVarProj e vars = 
          match vars with
          | [] -> Errors.unexpected ("Accessed variable '" + v + "'not in scope")
          | x::xs when x = v -> !builtin("fst", []) |@| e
          | x::xs -> getVarProj (!builtin("snd", []) |@| e) xs
        getVarProj (!builtin("counit", [c]) |@| ctx) vars

    | Expr.App(e1, e2) ->
        let r, s, t = coeff e1, coeff e2, match typ e1 with Type.Func((c, _), _, _) -> c | _ -> Errors.unexpected "Expected a function on the left-hand-side in application."
        let ctx0, ctx1, ctx2 = freshName "ctx", freshName "ctx", freshName "ctx"
        // Split context for evaluating `e1` and `e2` composed with the function call
        let ctxSplit = !builtin("split", [r; s ** t]) |@| (!builtin("duplicate", [r ++ (s ** t)]) |@| ctx)
        let fn = !Expr.Fun(!!Pattern.Var(ctx0), translate (!Expr.Var(ctx0)) vars e2)
        let cobind = !builtin("cobind", [s; t]) |@| fn |@| !Expr.Var(ctx2)
        let body = translate (!Expr.Var(ctx1)) vars e1 |@| cobind
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var(ctx1); !!Pattern.Var(ctx2)]), ctxSplit, body)

    | Expr.Fun(TypedPat(_, Pattern.Var v), e) ->
        let r, s = c, match t with Type.Func((c, _), _, _) -> c | _ -> Errors.unexpected "Expected a function type for a function expression."
        let ctx0 = freshName "ctx"
        let merged = !Expr.App(!builtin("merge", [s; r]), !Expr.Tuple([!Expr.Var(v); ctx]))
        !Expr.Fun(!!Pattern.Var(v), 
            !Expr.Let(!!Pattern.Var(ctx0), merged, translate (!Expr.Var(ctx0)) (v::vars) e))

    | Expr.Let(TypedPat(_, Pattern.Var v), e1, e2) -> 
        // The translation follows abs/app pair, but with optimized 'let' coeffects:
        //   let ctx1, ctx2 = split [s, r*s] (duplicate [s + (r * s)] ctx)
        //   [ @ s |- e2 ] (merge [s,s] (cobind [r,s] (fun ctx -> [ @ r |- e1 ] ctx) ctx2, ctx1))
        let r, s = coeff e1, coeff e2
        let ctxSplit = !builtin("split", [s; r ** s]) |@| (!builtin("duplicate", [s ++ (r ** s)]) |@| ctx)
        let ctx0, ctx1, ctx2 = freshName "ctx", freshName "ctx", freshName "ctx"
        let fn = !Expr.Fun(!!Pattern.Var(ctx0), translate (!Expr.Var(ctx0)) vars e1)
        let cobind = !builtin("cobind", [r; s]) |@| fn |@| !Expr.Var(ctx2)
        let merged = !builtin("merge", [s; s]) |@| !Expr.Tuple([cobind; !Expr.Var(ctx1)])
        let body = translate merged (v::vars) e2
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var(ctx1); !!Pattern.Var(ctx2)]), ctxSplit, body)

    | Expr.Binary(op, e1, e2) ->
        let r, s = coeff e1, coeff e2
        let ctx1, ctx2 = freshName "ctx", freshName "ctx"
        let ctxSplit = !builtin("split", [r; s]) |@| (!builtin("duplicate", [r ++ s]) |@| ctx)
        let body = !Expr.Binary(op, translate (!Expr.Var(ctx1)) vars e1, translate (!Expr.Var(ctx2)) vars e2)
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var(ctx1); !!Pattern.Var(ctx2)]), ctxSplit, body)

    // DATAFLOW AND IMPLICIT PARAMETERS
    | Expr.Prev(e) ->
        let r, r' = match c with Coeffect.Past n -> Coeffect.Past n, Coeffect.Past (n-1) | _ -> Errors.unexpected "Unexpected coeffect in the prev expression."
        translate (!builtin("prev", [r; r']) |@| ctx) vars e

    | Expr.QVar(v) ->
        !builtin("lookup", [Coeffect.ImplicitParam(v, translateType t)]) |@| ctx

    | Expr.Let(TypedPat((_, _, vt), Pattern.QVar v), e1, e2) -> 
        // There is no cobind, because we are not composing functions. Just split the 
        // context, call `letimpl` on one part of it and pass the result to `e2`:
        //
        //   let ctx1, ctx2 = split [s, r*s] (duplicate [s + (r * s)] ctx)
        //   [ @ s |- e2 ] (letimpl [?a:A,s] (ctx1, [ @ r |- e1 ] ctx2))
        //
        // Also, s' might not actually contain ?v (implicit subcoeffecting)
        // and so we pass both s and s' to `letimpl` so that it can 
        // produce the right comonad value as the result
        let r, s', s = coeff e1, coeff e2, removeImplicit (v, vt) (coeff e2)
        let ctx0, ctx1, ctx2 = freshName "ctx", freshName "ctx", freshName "ctx"
        let ctxSplit = !builtin("split", [s; r]) |@| (!builtin("duplicate", [s ++ r]) |@| ctx)      
        let arg = translate (!Expr.Var(ctx2)) vars e1
        let merged = !builtin("letimpl", [Coeffect.ImplicitParam(v, vt); s; s']) |@| !Expr.Tuple([!Expr.Var(ctx1); arg])
        let body = !Expr.Let(!!Pattern.Var(ctx0), merged, translate (!Expr.Var(ctx0)) vars e2)
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var(ctx1); !!Pattern.Var(ctx2)]), ctxSplit, body)
      
    // NOT SUPPORTED
    | Expr.Tuple _
    | Expr.Builtin  _ 
    | Expr.Let(_, _, _)
    | Expr.Fun(_, _) -> Errors.unexpected "The expression is not supproted in the source language."

// ------------------------------------------------------------------------------------------------
// Translation for structural coeffects
// ------------------------------------------------------------------------------------------------

module Structural =
  /// Workaround for FunScript bug (choose reverses order of things) 
  let choose f xs =
    List.fold (fun acc x -> match f x with Some y -> y::acc | None -> acc) [] xs |> List.rev
 
  /// Create a builtin primitive with structural coeffect annotation
  let builtin (s, ans) = Expr.Builtin (s, [ for a in ans -> Annotation.Structural(a)])

  /// Transforms the context represented by an expression `ctx` and containing
  /// variables with coeffects as specified by `vars` into a new context containing
  /// just variables that are bound in `coeff`.
  let transformContext ctx (vars:list<string * Coeffect>) (coeff:CoeffVars) =
    // Generate flags (which vars are included), source & target coeffects for them
    let flags = vars |> List.map (fun (v, _) -> if coeff.ContainsKey v then "1" else "0")
    let coeffs = vars |> choose (fun (v, c1) -> coeff.TryFind v |> Option.map (fun (c2, _) -> v, (c1, c2)))
    let coeffs1, coeffs2 = List.map (snd >> fst) coeffs, List.map (snd >> snd) coeffs
    let newVars = coeffs |> List.map (fun (v, (_, c)) -> v, c)
    !builtin("choose_" + String.concat "" flags, [coeffs1; coeffs2]) |@| ctx, newVars

  /// Implements structural coeffect translation. Takes a fresh name generator for
  /// naming 'ctx' variables, expression representing the current context and a
  /// list of variables in the 'ctx' environment and their coeffects.
  let rec translate freshName ctx (vars:list<string * Coeffect>) (Typed((cv:CoeffVars,c,t), e)) = 
    let translate = translate freshName 

    // Filter out variables that are not used in this sub-expression
    let ctx, vars = transformContext ctx vars cv
  
    // CORE EXPRESSIONS (VAR, CONST, APP, ABS)
    match e with
    | Expr.Number(n) ->
        !Expr.Number(n)

    | Expr.Var(v) ->
        // Structural coeffects should only have one variable in context by now
        if cv |> Map.toList |> List.map fst <> [v] then 
          Errors.unexpected "Expected just one variable in the context"
        let c = [ fst (cv.[v]) ]
        !builtin("counit", [c]) |@| ctx

    | Expr.Fun(TypedPat(_, Pattern.Var v), e) ->
        let varC, varT = match t with Type.Func((_, c), t, _) -> c, t | _ -> Errors.unexpected "Expected a function type for a function expression."
        let r = [ for v, _ in vars -> fst (cv.[v]) ]
        let s = [ varC ]
        let ctx0 = freshName "ctx"
        let merged = !Expr.App(!builtin("merge", [s; r]), !Expr.Tuple([!Expr.Var(v); ctx]))
        !Expr.Fun(!!Pattern.Var(v), 
          !Expr.Let(!!Pattern.Var(ctx0), merged, translate (!Expr.Var(ctx0)) ((v, varC)::vars) e))

    | Expr.Binary(op, e1, e2) ->
        // Recursive call takes care of splitting variables and their coeffects
        !Expr.Binary(op, translate ctx vars e1, translate ctx vars e2)

    | Expr.App(e1, e2) ->
        let t = match typ e1 with Type.Func((_, c), _, _) -> c | _ -> Errors.unexpected "Expected a function on the left-hand-side in application."
        let (ctx1, vars1), (ctx2, vars2) = 
          transformContext ctx vars (cvars e1), 
          transformContext ctx vars (Map.map (fun _ (s, typ) -> s ** t, typ) (cvars e2))
        let _, vars2' = transformContext ctx vars (cvars e2)
        let s = List.map snd vars2'

        let cobind = 
          let ctx0 = freshName "ctx"
          let fn = !Expr.Fun(!!Pattern.Var(ctx0), translate (!Expr.Var(ctx0)) vars2' e2)
          !builtin("cobind", [s; [t]]) |@| fn |@| ctx2
        translate ctx1 vars1 e1 |@| cobind

    | Expr.Let(TypedPat(_, Pattern.Var v) as p, e1, e2) -> 
        let varC, varT = (cvars e2).[v]
        let tinfos = Map.remove v (cvars e2), Coeffect.None, Type.Func((Coeffect.None, varC), varT, t)
        translate ctx vars (Typed((cv,c,t), Expr.App(Typed.Typed(tinfos, Expr.Fun(p, e2)), e1)))

    // DATAFLOW COEFFECT CONSTRUCTS
    | Expr.Prev(e) ->
        let infos = [ for v, c in vars -> match c with Coeffect.Past n -> c, Coeffect.Past(n-1), v | _ -> Errors.unexpected "Unexpected coeffect in the prev expression."]
        let r = [ for c, _ , _ in infos -> c ]
        let r' = [ for _, c, _ in infos -> c ]
        let vars = [ for _, c, v in infos -> v, c ]
        translate (!builtin("prev", [r; r']) |@| ctx) vars e

    // NOT SUPPORTED
    | Expr.QVar _
    | Expr.Tuple _
    | Expr.Builtin  _ 
    | Expr.Let(_, _, _)
    | Expr.Fun(_, _) -> Errors.unexpected "The expression is not supproted in the source language."


// ------------------------------------------------------------------------------------------------
// Typing for built-in operations and main translation function
// ------------------------------------------------------------------------------------------------

/// Workaround for FunScript bug (filter reverses order of things) 
let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 

/// Returns types of builtin operations
let builtins inputCoeffect (ctx:TypeChecker.InputContext) (n, c:Annotation list) = 

  // Generating new type & coeffect variables
  let cvar() = Coeffect.Variable(ctx.NewCoeffectVar())
  let tvar() = Type.Variable(ctx.NewTypeVar())
  let ttvar (c:list<Coeffect>) = Type.Tuple [for _ in c -> tvar()]
  
  // Helpers for building types
  let ( --> ) l r = Type.Func((Coeffect.Use, Coeffect.None), l, r)
  let ( * ) l r = Type.Tuple [l; r]
  let ( *@* ) l r = 
    match l, r with 
    | Type.Tuple l, Type.Tuple r -> Type.Tuple (l @ r) 
    | _ -> Errors.unexpected "Merge expects two tuples."
  let Cf c t = Type.FlatComonad(c, t)
  let Cs c t = Type.StructuralComonad(c, t)

  match n, c with
  // DATAFLOW AND IMPLICIT PARAMS
  | "lookup", [Annotation.Flat(Coeffect.ImplicitParam(n, t) as c)] -> 
      Cf c (tvar()) --> t
  | "letimpl", [Annotation.Flat(Coeffect.ImplicitParam(_, t)); Annotation.Flat s; Annotation.Flat s'] ->
      let a = tvar()
      Cf s a * t --> Cf s' a
  | "prev", [Annotation.Flat r; Annotation.Flat r'] ->
      let a = tvar() 
      Cf r a --> Cf r' a

  // FLAT COEFFECTS
  | "merge", [Annotation.Flat r; Annotation.Flat s] -> 
      let a, b = tvar(), tvar()
      Cf r a * Cf s b --> Cf (r ^^ s) (a * b)
  | "split", [Annotation.Flat r; Annotation.Flat s] ->
      let a, b = tvar(), tvar()
      Cf (r ++ s) (a * b) --> Cf r a * Cf s b
  | "duplicate", [Annotation.Flat r] ->
      let a = tvar()
      Cf r a --> Cf r (a * a)
  | "cobind", [Annotation.Flat r; Annotation.Flat s] ->
      let a, b = tvar(), tvar()
      (Cf r a --> b) --> (Cf (r ** s) a --> Cf s b)
  | "counit", [Annotation.Flat(Coeffect.Use | Coeffect.Past 0)] ->
      let a = tvar()
      Cf Coeffect.Use a --> a
  | "finput", [] -> Cf inputCoeffect (Type.Primitive "unit")

  // STRUCTURAL COEFFECTS
  | "sinput", [] -> Cs [] (Type.Tuple [])
  | "prev", [Annotation.Structural r; Annotation.Structural r'] ->
      let a = ttvar r
      Cs r a --> Cs r' a
  | "cobind", [Annotation.Structural r; Annotation.Structural [s]] ->
      let a, b = ttvar r, tvar()
      (Cs r a --> b) --> (Cs [ for r in r -> r ** s ] a --> Cs [s] (Type.Tuple [b]))
  | "counit", [Annotation.Structural [Coeffect.Use | Coeffect.Past 0]] ->
      let a = tvar()
      Cs [Coeffect.Use] (Type.Tuple [a]) --> a
  | "merge", [Annotation.Structural r; Annotation.Structural s] -> 
      let a, b = ttvar r, ttvar s
      Cs r a * Cs s b --> Cs (r @ s) (a *@* b)
  | str, [Annotation.Structural cs1; Annotation.Structural cs2] when str.StartsWith("choose_") -> 
      // e.g. choose_101 [c1; c2] [c1'; c2'] : C <c1, _, c2> (a * b * c) -> C <c1', c2'> (a * c)
      let csin = ref (List.zip cs1 cs2)
      let next() = let res = List.head csin.Value in csin.Value <- List.tail csin.Value; res
      let infos = 
        [ for c in str.Substring("choose_".Length).ToCharArray() -> 
          if c = '1' then true, tvar(), next() else false, tvar(), (let c = cvar() in c, c) ]
      let inputs = infos |> List.map (fun (_, t, c) -> t, fst c)
      let outputs = infos |> filter (fun (i, _, _) -> i) |> List.map (fun (_, t, c) -> t, snd c)
      Cs (List.map snd inputs) (Type.Tuple (List.map fst inputs))
        --> Cs (List.map snd outputs) (Type.Tuple (List.map fst outputs))

  // NON-COEFFECTFUL OPERATIONS
  | "fst", [] ->
      let a, b = tvar(), tvar()
      a * b --> a
  | "snd", [] ->
      let a, b = tvar(), tvar()
      a * b --> b
  | _ -> Errors.unexpected ("Unexpected builting primitive '" + n + "'")


/// Returns a generator of fresh names that returns 0, .., 9, A, .. Z, 10, 11, 12, ...
let newFreshName () = 
  let counter = ref 0
  fun s ->
    incr counter
    let n = counter.Value
    if n <= 9 then s + string n
    elif n <= 35 then s + (char (55 + n)).ToString()
    else s + string (n - 26)

/// Simplify expression - contracts eta and nested 'choose' calls
let rec contract (Typed(t, e)) = 
  let again, contracted = 
    match e with
    | Expr.Fun(TypedPat(_, Pattern.Var v1), Typed(tb, Expr.App(e1, Typed(ta, Expr.Var v2)))) when v1 = v2 ->
        true, contract e1
    | Expr.App(Typed(_, Expr.Builtin(str, [Annotation.Structural cs1; Annotation.Structural cs2])), earg) when 
        str.StartsWith("choose_") && cs1 = cs2 && str.Substring("choose_".Length).ToCharArray() |> Array.forall ((=) '1') -> 
        true, contract earg
    | ExprShape.Nested(s, es) -> 
        false, Typed(t, ExprShape.recreate s (List.map contract es))
    | e -> false, Typed(t, e)
  if again then contract contracted
  else contracted

/// Translate expression using specified mode and kind
let translate mode kind typed =
  let fn = newFreshName ()
  let transle  = 
    if mode = CoeffectMode.Flat then Flat.translate fn (Typed((), Expr.Builtin("finput", []))) [] typed 
      else Structural.translate fn (Typed((), Expr.Builtin("sinput", []))) [] typed 
  transle
  |> contract
  |> TypeChecker.typeCheck (builtins (TypeChecker.coeff typed)) (CoeffectKind.Embedded kind) CoeffectMode.None

