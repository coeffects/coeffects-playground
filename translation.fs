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

let rec translate ctx vars (Typed((v,c,t), e)) = 
  match e with
  | Expr.Number(n) ->
      !Expr.Number(n)
  | Expr.Var(v) ->
      // (v1, (v2, (v3, ()))
      let rec getVarProj e vars = 
        match vars with
        | [] -> failwith "Variable not in scope"
        | x::xs when x = v -> !Expr.Builtin("fst", []) |@| e
        | x::xs -> getVarProj (!Expr.Builtin("snd", []) |@| e) xs
      getVarProj (!Expr.Builtin("counit", [c]) |@| ctx) vars

  | Expr.QVar(v) ->
      !Expr.Builtin("lookup", [Coeffect.ImplicitParam(v, t)]) |@| ctx

  | Expr.App(e1, e2) ->
      let r, s, t = coeff e1, coeff e2, match typ e1 with Type.Func((c, _), _, _) -> c | _ -> failwith "Not a function!"        
      let ctxSplit = !Expr.Builtin("split", [r; s ** t]) |@| (!Expr.Builtin("duplicate", [r ++ (s ** t)]) |@| ctx)
      let fn = !Expr.Fun(!!Pattern.Var("ctx"), translate (!Expr.Var("ctx")) vars e2)
      let cobind = !Expr.Builtin("cobind", [s; t]) |@| fn |@| !Expr.Var("ctx2")
      let body = translate (!Expr.Var("ctx1")) vars e1 |@| cobind
      !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

  | Expr.Fun(TypedPat(_, Pattern.Var v), e) ->
      let r, s = c, match t with Type.Func((c, _), _, _) -> c | _ -> failwith "Not a function!"
      let merged = Expr.App(!Expr.Builtin("merge", [s; r]), !Expr.Tuple([!Expr.Var(v); ctx]))
      !Expr.Fun(!!Pattern.Var(v), translate (!merged) (v::vars) e)

  | Expr.Let(TypedPat(_, Pattern.Var v), e1, e2) -> 
      // let <v> = <e1> in <e2>
      //
      // let ctx1, ctx2 = split [s, r*s] (duplicate [s + (r * s)] ctx)
      // [ @ s |- e2 ] (merge [s,s] (cobind [r,s] (fun ctx -> [ @ r |- e1 ] ctx) ctx2, ctx1))
      let r, s = coeff e1, coeff e2
      let ctxSplit = !Expr.Builtin("split", [s; r ** s]) |@| (!Expr.Builtin("duplicate", [s ++ (r ** s)]) |@| ctx)
      let fn = !Expr.Fun(!!Pattern.Var("ctx"), translate (!Expr.Var("ctx")) vars e1)
      let cobind = !Expr.Builtin("cobind", [r; s]) |@| fn |@| !Expr.Var("ctx2")
      let merged = !Expr.Builtin("merge", [s; s]) |@| !Expr.Tuple([cobind; !Expr.Var("ctx1")])
      let body = translate merged (v::vars) e2
      !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

  | Expr.Binary(op, e1, e2) ->
      let r, s = coeff e1, coeff e2
      let ctxSplit = !Expr.Builtin("split", [r; s]) |@| (!Expr.Builtin("duplicate", [r ++ s]) |@| ctx)
      let body = !Expr.Binary(op, translate (!Expr.Var("ctx1")) vars e1, translate (!Expr.Var("ctx2")) vars e2)
      !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)

  | Expr.Prev(e) ->
      let r, r' = match c with Coeffect.Past n -> Coeffect.Past n, Coeffect.Past (n-1) | _ -> failwith "Unexpected coeffect in prev."
      translate (!Expr.Builtin("prev", [r; r']) |@| ctx) vars e

  | Expr.Let(TypedPat((_, _, vt), Pattern.QVar v), e1, e2) -> 
      // let <?a> = <e1> in <e2>
      //
      // let ctx1, ctx2 = split [s, r*s] (duplicate [s + (r * s)] ctx)
      // [ @ s |- e2 ] (letimpl [?a:A,s] (ctx1, [ @ r |- e1 ] ctx2))

      // s' might not actually contain ?v (implicit subcoeffecting)
      // and so we pass both s and s' to letimpl so that it can 
      // produce the right comonad value as the result

      let r, s', s = coeff e1, coeff e2, removeImplicit (v, vt) (coeff e2)
      let ctxSplit = !Expr.Builtin("split", [s; r]) |@| (!Expr.Builtin("duplicate", [s ++ r]) |@| ctx)      
      let arg = translate (!Expr.Var("ctx2")) vars e1
      let merged = !Expr.Builtin("letimpl", [Coeffect.ImplicitParam(v, vt); s; s']) |@| !Expr.Tuple([!Expr.Var("ctx1"); arg])
      let body = translate merged (vars) e2
      !Expr.Let(!!Pattern.Tuple([!!Pattern.Var("ctx1"); !!Pattern.Var("ctx2")]), ctxSplit, body)
      
  | Expr.Tuple _
  | Expr.Builtin _ 
  | Expr.Let(_, _, _)
  | Expr.Fun(_, _) ->
      failwith "Not supported"
    

let rec contract (Typed(t, e)) = 
  match e with
  | Expr.Fun(TypedPat(_, Pattern.Var v1), Typed(tb, Expr.App(e1, Typed(ta, Expr.Var v2)))) when v1 = v2 ->
      contract e1
  | ExprShape.Nested(s, es) -> Typed(t, ExprShape.recreate s (List.map contract es))
  | e -> Typed(t, e)


let builtins inputCoeffect (ctx:TypeChecker.InputContext) (n, c) = 
  let cvar() = Coeffect.Variable(ctx.NewCoeffectVar())
  let tvar() = Type.Variable(ctx.NewTypeVar())
  let ( --> ) l r = Type.Func((Coeffect.Use, Coeffect.None), l, r)
  let ( * ) l r = Type.Tuple [l; r]
  let C c t = Type.Comonad(c, t)
  match n, c with
  | "lookup", [Coeffect.ImplicitParam(n, t) as c] -> 
      C c (tvar()) --> t
  | "letimpl", [Coeffect.ImplicitParam(_, t); s; s'] ->
      let a = tvar()
      C s a * t --> C s' a // It's only implicits so pick ++ randomly (all are union anyway)
  | "prev", [r; r'] ->
      let a = tvar() 
      C r a --> C r' a

  | "merge", [r; s] -> 
      let a, b = tvar(), tvar()
      C r a * C s b --> C (r ^^ s) (a * b)
  | "split", [r; s] ->
      let a, b = tvar(), tvar()
      C (r ++ s) (a * b) --> C r a * C s b
  | "duplicate", [r] ->
      let a = tvar()
      C r a --> C r (a * a)
  | "cobind", [r; s] ->
      let a, b = tvar(), tvar()
      (C r a --> b) --> (C (r ** s) a --> C s b)
  | "counit", [Coeffect.Use | Coeffect.Past 0] ->
      let a = tvar()
      C Coeffect.Use a --> a

  | "input", [] ->
      C inputCoeffect (Type.Primitive "unit")
  | "fst", [] ->
      let a, b = tvar(), tvar()
      a * b --> a
  | "snd", [] ->
      let a, b = tvar(), tvar()
      a * b --> b
  | _ -> failwith ("Builtin: " + n) //failwith ("Builtin: " + n + "\n" + sprintf "%A" c)
