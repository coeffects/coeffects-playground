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
  let Builtin(s, ans) = Expr.Builtin(s, [ for a in ans -> Annotation.Structural(a)])

  let rec translate (ctx:option<_>) vars (Typed((cv:CoeffVars,_,t), e)) = 
    
    let ctx, vars = 
      match ctx, vars with
      | None, [] -> ctx, []
      | None, _ -> failwith "Expected empty variables"
      | Some ctx, vars when vars |> List.forall cv.ContainsKey -> Some ctx, vars
      | Some ctx, vars ->
          let flags = [ for v in vars -> if cv.ContainsKey v then "1" else "0" ] 
          let coeffs = [ for v in vars do match cv.TryFind v with Some c -> yield fst c | _ -> () ] 
          Some(!Builtin("choose_" + String.concat "" flags, [coeffs]) |@| ctx), [ for v in vars do if cv.ContainsKey v then yield v ]

    match e with
    | Expr.Number(n) ->
        !Expr.Number(n)

    | Expr.Var(v) ->
        if cv |> Map.toList |> List.map fst <> [v] then failwith "Expected just one variable"        
        let c = [ fst (cv.[v]) ]
        !Builtin("counit", [c]) |@| ctx.Value

    | Expr.Fun(TypedPat(_, Pattern.Var v), e) ->
        let r = [ for v in vars -> fst (cv.[v]) ]
        let s = [ (match t with Type.Func((_, c), _, _) -> c | _ -> failwith "Not a function!") ]
        let merged = 
          match ctx with 
          | Some ctx -> Expr.App(!Builtin("merge", [s; r]), !Expr.Tuple([!Expr.Var(v); ctx]))
          | None -> Expr.Var(v)
        !Expr.Fun(!!Pattern.Var(v), translate (Some (!merged)) (v::vars) e)

    | Expr.Prev(e) ->
        let r = [ for v in vars -> fst (cv.[v]) ]
        let r' = [ for v in vars -> match fst (cv.[v]) with Coeffect.Past n -> Coeffect.Past(n-1) | _ -> failwith "Unexpected coeffect in prev."]
        translate (ctx |> Option.map (fun ctx -> !Builtin("prev", [r; r']) |@| ctx)) vars e

    | Expr.Binary(op, e1, e2) ->
        !Expr.Binary(op, translate ctx vars e1, translate ctx vars e2)

    // App, Fun, Let

    | Expr.QVar _
    | Expr.Tuple _
    | Expr.Builtin _ 
    | Expr.Let(_, _, _)
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
  | ExprShape.Nested(s, es) -> Typed(t, ExprShape.recreate s (List.map contract es))
  | e -> Typed(t, e)


let builtins inputCoeffect (ctx:TypeChecker.InputContext) (n, c:Annotation list) = 
  let cvar() = Coeffect.Variable(ctx.NewCoeffectVar())
  let tvar() = Type.Variable(ctx.NewTypeVar())
  let ttvar (c:list<Coeffect>) = Type.Tuple [for _ in c -> tvar()]
  let ( --> ) l r = Type.Func((Coeffect.Use, Coeffect.None), l, r)
  let ( * ) l r = Type.Tuple [l; r]
  let ( *@* ) l r = match l, r with Type.Tuple l, Type.Tuple r -> Type.Tuple (l @ r) | _ -> failwith "Expected tuple!!"
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
  | "input", [] ->
      Cf inputCoeffect (Type.Primitive "unit")

  // Structural
  | "prev", [Annotation.Structural r; Annotation.Structural r'] ->
      let a = ttvar r
      Cs r a --> Cs r' a

  | "counit", [Annotation.Structural [Coeffect.Use | Coeffect.Past 0]] ->
      let a = tvar()
      Cs [Coeffect.Use] a --> a
  | "merge", [Annotation.Structural r; Annotation.Structural s] -> 
      let a, b = ttvar r, ttvar s
      Cs r a * Cs s b --> Cs (r @ s) (a *@* b)

  | str, [Annotation.Structural cs] when str.StartsWith("choose_") -> 
      // e.g. choose_101 [c1; c2] : C <c1, _, c2> (a * b * c) -> C <c1, c2> (a * c)
      let csin = ref cs
      let next() = let res = List.head csin.Value in csin.Value <- List.tail csin.Value; res
      let infos = 
        [ for c in str.Substring("choose_".Length).ToCharArray() -> 
          if c = '1' then true, tvar(), next() else false, tvar(), cvar() ]
      let inputs = infos |> List.map (fun (_, t, c) -> t, c)
      let outputs = infos |> List.filter (fun (i, _, _) -> i) |> List.map (fun (_, t, c) -> t, c)
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
