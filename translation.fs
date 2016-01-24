// ------------------------------------------------------------------------------------------------
// Coeffect translation that translates source language to a target langauge with comonads
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Translation
open Coeffects
open Coeffects.Ast

let (!) e = Typed((), e)
let (!!) p = TypedPat((), p)
let (|@|) a b = !Expr.App(a, b)
let cvars (Typed((c, _, _), _)) : CoeffVars = c
let coeff (Typed((_, c, _), _)) = c
let typ (Typed((_, _, t), _)) = t

let ( ^^ ) l r = Coeffect.Merge(l, r)
let ( ++ ) l r = Coeffect.Split(l, r)
let ( ** ) l r = Coeffect.Seq(l, r)

let rec removeImplicit (v, vt) coeff = 
  match coeff with
  | Coeffect.Split(nested, Coeffect.ImplicitParam(n, nt)) when n = v -> nested
  | Coeffect.Split(nested, Coeffect.ImplicitParam(n, nt)) -> Coeffect.Split(removeImplicit (v, vt) nested, Coeffect.ImplicitParam(n, nt))
  | Coeffect.Use -> Coeffect.Use
  | _ -> failwith "Unexpected coeffect shape."

module Flat = 
  let Builtin(s, ans) = Expr.Builtin(s, [ for a in ans -> Annotation.Flat(a)])

  let rec translate ctx vars (Typed((v,c,t), e)) = 
    match e with
    | Expr.Number(n) ->
        !Expr.Number(n)

    | Expr.Var(v) ->
        // (v1, (v2, (v3, ()))
        let rec getVarProj e vars = 
          match vars with
          | [] -> failwith "Variable not in scope"
          | x::xs when x = v -> !Builtin("fst", []) |@| e
          | x::xs -> getVarProj (!Builtin("snd", []) |@| e) xs
        getVarProj (!Builtin("counit", [c]) |@| ctx) vars

    | Expr.QVar(v) ->
        !Builtin("lookup", [Coeffect.ImplicitParam(v, t)]) |@| ctx

    | Expr.App(e1, e2) ->
        let r, s, t = coeff e1, coeff e2, match typ e1 with Type.Func((c, _), _, _) -> c | _ -> failwith "Not a function!"        
        let ctxSplit = !Builtin("split", [r; s ** t]) |@| (!Builtin("duplicate", [r ++ (s ** t)]) |@| ctx)
        let fn = !Expr.Fun(!!Pattern.Var("ctx"), translate (!Expr.Var("ctx")) vars e2)
        let cobind = !Builtin("cobind", [s; t]) |@| fn |@| !Expr.Var("ctx2")
        let body = translate (!Expr.Var("ctx1")) vars e1 |@| cobind
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

    | Expr.Fun(TypedPat(_, Pattern.Var v), e) ->
        let r, s = c, match t with Type.Func((c, _), _, _) -> c | _ -> failwith "Not a function!"
        let merged = Expr.App(!Builtin("merge", [s; r]), !Expr.Tuple([!Expr.Var(v); ctx]))
        !Expr.Fun(!!Pattern.Var(v), translate (!merged) (v::vars) e)

    | Expr.Let(TypedPat(_, Pattern.Var v), e1, e2) -> 
        // let <v> = <e1> in <e2>
        //
        // let ctx1, ctx2 = split [s, r*s] (duplicate [s + (r * s)] ctx)
        // [ @ s |- e2 ] (merge [s,s] (cobind [r,s] (fun ctx -> [ @ r |- e1 ] ctx) ctx2, ctx1))
        let r, s = coeff e1, coeff e2
        let ctxSplit = !Builtin("split", [s; r ** s]) |@| (!Builtin("duplicate", [s ++ (r ** s)]) |@| ctx)
        let fn = !Expr.Fun(!!Pattern.Var("ctx"), translate (!Expr.Var("ctx")) vars e1)
        let cobind = !Builtin("cobind", [r; s]) |@| fn |@| !Expr.Var("ctx2")
        let merged = !Builtin("merge", [s; s]) |@| !Expr.Tuple([cobind; !Expr.Var("ctx1")])
        let body = translate merged (v::vars) e2
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

    | Expr.Binary(op, e1, e2) ->
        let r, s = coeff e1, coeff e2
        let ctxSplit = !Builtin("split", [r; s]) |@| (!Builtin("duplicate", [r ++ s]) |@| ctx)
        let body = !Expr.Binary(op, translate (!Expr.Var("ctx1")) vars e1, translate (!Expr.Var("ctx2")) vars e2)
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

    | Expr.Prev(e) ->
        let r, r' = match c with Coeffect.Past n -> Coeffect.Past n, Coeffect.Past (n-1) | _ -> failwith "Unexpected coeffect in prev."
        translate (!Builtin("prev", [r; r']) |@| ctx) vars e

    | Expr.Let(TypedPat((_, _, vt), Pattern.QVar v), e1, e2) -> 
        // let <?a> = <e1> in <e2>
        //
        // let ctx1, ctx2 = split [s, r*s] (duplicate [s + (r * s)] ctx)
        // [ @ s |- e2 ] (letimpl [?a:A,s] (ctx1, [ @ r |- e1 ] ctx2))

        // s' might not actually contain ?v (implicit subcoeffecting)
        // and so we pass both s and s' to letimpl so that it can 
        // produce the right comonad value as the result

        let r, s', s = coeff e1, coeff e2, removeImplicit (v, vt) (coeff e2)
        let ctxSplit = !Builtin("split", [s; r]) |@| (!Builtin("duplicate", [s ++ r]) |@| ctx)      
        let arg = translate (!Expr.Var("ctx2")) vars e1
        let merged = !Builtin("letimpl", [Coeffect.ImplicitParam(v, vt); s; s']) |@| !Expr.Tuple([!Expr.Var("ctx1"); arg])
        let body = translate merged (vars) e2
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)
      
    | Expr.Tuple _
    | Expr.Builtin _ 
    | Expr.Let(_, _, _)
    | Expr.Fun(_, _) ->
        failwith "Not supported"

module Structural = 
  let choose f xs =
    List.fold (fun acc x -> match f x with Some y -> y::acc | None -> acc) [] xs |> List.rev
 
  let Builtin(s, ans) = Expr.Builtin(s, [ for a in ans -> Annotation.Structural(a)])

  /// Transforms the context represented by an expression `ctx` and containing
  /// variables with coeffects as specified by `vars` into a new context containing
  /// just variables that are bound in `coeff`.
  let transformContext ctx (vars:list<string * Coeffect>) (coeff:CoeffVars) =
    // Generate flags (which vars are included), source & target coeffects for them
    let flags = vars |> List.map (fun (v, _) -> if coeff.ContainsKey v then "1" else "0")
    let coeffs = vars |> choose (fun (v, c1) -> coeff.TryFind v |> Option.map (fun (c2, _) -> v, (c1, c2)))
    let coeffs1, coeffs2 = List.map (snd >> fst) coeffs, List.map (snd >> snd) coeffs
    let newVars = coeffs |> List.map (fun (v, (_, c)) -> v, c)
    !Builtin("choose_" + String.concat "" flags, [coeffs1; coeffs2]) |@| ctx, newVars

  let rec translate ctx (vars:list<string * Coeffect>) (Typed((cv:CoeffVars,c,t), e)) = 
    
    let ctx, vars = transformContext ctx vars cv
  
    match e with
    | Expr.Number(n) ->
        !Expr.Number(n)

    | Expr.Var(v) ->
        if cv |> Map.toList |> List.map fst <> [v] then failwith "Expected just one variable"        
        let c = [ fst (cv.[v]) ]
        !Builtin("counit", [c]) |@| ctx

    | Expr.Fun(TypedPat(_, Pattern.Var v), e) ->
        let r = [ for v, _ in vars -> fst (cv.[v]) ]
        let varC, varT = match t with Type.Func((_, c), t, _) -> c, t | _ -> failwith "Not a function!"
        let s = [ varC ]
        let merged = 
          Expr.App(!Builtin("merge", [s; r]), !Expr.Tuple([!Expr.Var(v); ctx]))

        !Expr.Fun(!!Pattern.Var(v), translate (!merged) ((v, varC)::vars) e)

    | Expr.Prev(e) ->
        let infos = [ for v, c in vars -> match c with Coeffect.Past n -> c, Coeffect.Past(n-1), v | _ -> failwith "Unexpected coeffect in prev." ]
        let r = [ for c, _ , _ in infos -> c ]
        let r' = [ for _, c, _ in infos -> c ]
        let vars = [ for _, c, v in infos -> v, c ]
        translate (!Builtin("prev", [r; r']) |@| ctx) vars e

    | Expr.Binary(op, e1, e2) ->
        (*let r, s = coeff e1, coeff e2
        match ctx with
        | Some ctx ->
            let ctxSplit = !Builtin("split", [r; s]) |@| ctx
            let body = !Expr.Binary(op, translate (Some (!Expr.Var("ctx1"))) vars e1, translate (Some (!Expr.Var("ctx2"))) vars e2)
            !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)
        | None ->*)
            !Expr.Binary(op, translate ctx vars e1, translate ctx vars e2)

    // App, Let

    | Expr.App(e1, e2) ->
        let t = match typ e1 with Type.Func((_, c), _, _) -> c | _ -> failwith "Not a function!"        
        let (ctx1, vars1), (ctx2, vars2) = 
          transformContext ctx vars (cvars e1), 
          transformContext ctx vars (Map.map (fun _ (s, typ) -> s ** t, typ) (cvars e2))

        let _, vars2' = transformContext ctx vars (cvars e2)
        let s = List.map snd vars2'

        //let ctxSplit = !Builtin("split", [r; s ** t]) |@| (!Builtin("duplicate", [r ++ (s ** t)]) |@| ctx)
        let cobind = 
          let fn = !Expr.Fun(!!Pattern.Var("ctx"), translate (!Expr.Var("ctx")) vars2' e2)
          !Builtin("cobind", [s; [t]]) |@| fn |@| ctx2
        //let body = 
        translate ctx1 vars1 e1 |@| cobind
        //!Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

    | Expr.Let(TypedPat(_, Pattern.Var v) as p, e1, e2) -> 
        let varC, varT = (cvars e2).[v]
        let tinfos = Map.remove v (cvars e2), Coeffect.None, Type.Func((Coeffect.None, varC), varT, t)
        translate ctx vars (Typed((cv,c,t), Expr.App(Typed.Typed(tinfos, Expr.Fun(p, e2)), e1)))

    | Expr.QVar _
    | Expr.Tuple _
    | Expr.Builtin _ 
    | Expr.Fun(_, _) ->
        failwith "Not supported"
    //| _ -> failwith "!"


(*
    | Expr.Number(n) ->
        !Expr.Number(n)
    | Expr.Var(v) ->
        // (v1, (v2, (v3, ()))
        let rec getVarProj e vars = 
          match vars with
          | [] -> failwith "Variable not in scope"
          | x::xs when x = v -> !Builtin("fst", []) |@| e
          | x::xs -> getVarProj (!Builtin("snd", []) |@| e) xs
        getVarProj (!Builtin("counit", [c]) |@| ctx) vars

    | Expr.QVar(v) ->
        !Builtin("lookup", [Coeffect.ImplicitParam(v, t)]) |@| ctx

    | Expr.App(e1, e2) ->
        let r, s, t = coeff e1, coeff e2, match typ e1 with Type.Func((c, _), _, _) -> c | _ -> failwith "Not a function!"        
        let ctxSplit = !Builtin("split", [r; s ** t]) |@| (!Builtin("duplicate", [r ++ (s ** t)]) |@| ctx)
        let fn = !Expr.Fun(!!Pattern.Var("ctx"), translate (!Expr.Var("ctx")) vars e2)
        let cobind = !Builtin("cobind", [s; t]) |@| fn |@| !Expr.Var("ctx2")
        let body = translate (!Expr.Var("ctx1")) vars e1 |@| cobind
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

    | Expr.Let(TypedPat(_, Pattern.Var v), e1, e2) -> 
        // let <v> = <e1> in <e2>
        //
        // let ctx1, ctx2 = split [s, r*s] (duplicate [s + (r * s)] ctx)
        // [ @ s |- e2 ] (merge [s,s] (cobind [r,s] (fun ctx -> [ @ r |- e1 ] ctx) ctx2, ctx1))
        let r, s = coeff e1, coeff e2
        let ctxSplit = !Builtin("split", [s; r ** s]) |@| (!Builtin("duplicate", [s ++ (r ** s)]) |@| ctx)
        let fn = !Expr.Fun(!!Pattern.Var("ctx"), translate (!Expr.Var("ctx")) vars e1)
        let cobind = !Builtin("cobind", [r; s]) |@| fn |@| !Expr.Var("ctx2")
        let merged = !Builtin("merge", [s; s]) |@| !Expr.Tuple([cobind; !Expr.Var("ctx1")])
        let body = translate merged (v::vars) e2
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

    | Expr.Binary(op, e1, e2) ->
        let r, s = coeff e1, coeff e2
        let ctxSplit = !Builtin("split", [r; s]) |@| (!Builtin("duplicate", [r ++ s]) |@| ctx)
        let body = !Expr.Binary(op, translate (!Expr.Var("ctx1")) vars e1, translate (!Expr.Var("ctx2")) vars e2)
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

    | Expr.Prev(e) ->
        let r, r' = match c with Coeffect.Past n -> Coeffect.Past n, Coeffect.Past (n-1) | _ -> failwith "Unexpected coeffect in prev."
        translate (!Builtin("prev", [r; r']) |@| ctx) vars e

    | Expr.Let(TypedPat((_, _, vt), Pattern.QVar v), e1, e2) -> 
        // let <?a> = <e1> in <e2>
        //
        // let ctx1, ctx2 = split [s, r*s] (duplicate [s + (r * s)] ctx)
        // [ @ s |- e2 ] (letimpl [?a:A,s] (ctx1, [ @ r |- e1 ] ctx2))

        // s' might not actually contain ?v (implicit subcoeffecting)
        // and so we pass both s and s' to letimpl so that it can 
        // produce the right comonad value as the result

        let r, s', s = coeff e1, coeff e2, removeImplicit (v, vt) (coeff e2)
        let ctxSplit = !Builtin("split", [s; r]) |@| (!Builtin("duplicate", [s ++ r]) |@| ctx)      
        let arg = translate (!Expr.Var("ctx2")) vars e1
        let merged = !Builtin("letimpl", [Coeffect.ImplicitParam(v, vt); s; s']) |@| !Expr.Tuple([!Expr.Var("ctx1"); arg])
        let body = translate merged (vars) e2
        !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)
      
    | Expr.Tuple _
    | Builtin _ 
    | Expr.Let(_, _, _)
    | Expr.Fun(_, _) ->
        failwith "Not supported"
*)    

let rec contract (Typed(t, e)) = 
  match e with
  | Expr.Fun(TypedPat(_, Pattern.Var v1), Typed(tb, Expr.App(e1, Typed(ta, Expr.Var v2)))) when v1 = v2 ->
      contract e1
  | Expr.App(Typed(_, Expr.Builtin(str, [Annotation.Structural cs1; Annotation.Structural cs2])), earg) when 
      str.StartsWith("choose_") && cs1 = cs2 && str.Substring("choose_".Length).ToCharArray() |> Array.forall ((=) '1') -> 
      contract earg
  | ExprShape.Nested(s, es) -> Typed(t, ExprShape.recreate s (List.map contract es))
  | e -> Typed(t, e)

let filter f xs = List.foldBack (fun x xs -> if f x then x::xs else xs) xs [] 

let builtins inputCoeffect (ctx:TypeChecker.InputContext) (n, c:Annotation list) = 
  let cvar() = Coeffect.Variable(ctx.NewCoeffectVar())
  let tvar() = Type.Variable(ctx.NewTypeVar())
  let ttvar (c:list<Coeffect>) = Type.Tuple [for _ in c -> tvar()]
  let ( --> ) l r = Type.Func((Coeffect.Use, Coeffect.None), l, r)
  let ( * ) l r = Type.Tuple [l; r]
  let ( *@* ) l r = 
    match l, r with 
    | Type.Tuple l, Type.Tuple r -> Type.Tuple (l @ r) 
    | _ -> failwith "must be tuple!"
  let Cf c t = Type.FlatComonad(c, t)
  let Cs c t = Type.StructuralComonad(c, t)
  match n, c with
  | "lookup", [Annotation.Flat(Coeffect.ImplicitParam(n, t) as c)] -> 
      Cf c (tvar()) --> t
  | "letimpl", [Annotation.Flat(Coeffect.ImplicitParam(_, t)); Annotation.Flat s; Annotation.Flat s'] ->
      let a = tvar()
      Cf s a * t --> Cf s' a // It's only implicits so pick ++ randomly (all are union anyway)
  | "prev", [Annotation.Flat r; Annotation.Flat r'] ->
      let a = tvar() 
      Cf r a --> Cf r' a

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
  | "finput", [] ->
      Cf inputCoeffect (Type.Primitive "unit")

  // Structural
  | "sinput", [] ->
      Cs [] (Type.Tuple [])

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

  // Non-coeffectful
  | "fst", [] ->
      let a, b = tvar(), tvar()
      a * b --> a
  | "snd", [] ->
      let a, b = tvar(), tvar()
      a * b --> b
  | _ -> failwith ("Builtin: " + n) //failwith ("Builtin: " + n + "\n" + sprintf "%A" c)
