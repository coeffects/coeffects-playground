// ------------------------------------------------------------------------------------------------
// An interpreter that evaluates translated expressions (with comonad primitives)
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Evaluation

open Coeffects
open Coeffects.Ast

type Value =
  | Unit
  | Integer of int
  | Function of (Value -> Value)
  | Tuple of Value list

  | ImplicitsComonad of Value * Map<string, Value>
  | ListComonad of Value list

type EvaluationContext = 
  { Variables : Map<string, Value> 
    Kind : CoeffectKind }

let rec bind value (TypedPat(_, pattern)) vars = 
  match pattern, value with
  | Pattern.Var n, v -> Map.add n v vars
  | Pattern.Tuple pats, Value.Tuple vals when pats.Length = vals.Length ->
      List.zip pats vals |> List.fold (fun ctx (p, v) -> bind v p ctx) vars
  | _ -> failwith "Pattern does not match value"        

let operators = 
  Map.ofList [ "+", (+); "-", (-); "*", (*); "/", (/); "^", pown ] 

let restrict (m:Map<string, Value>) s = 
  Map.ofList [ for v in Set.toList s -> v, Map.find v m ]

//let (|Fail|) s v = failwithf "%s %A" s v
let (|Fail|) s _ = failwith s

let evalImplicits ctx (Typed(_, expr)) = 
  match expr with
  | Expr.Builtin("merge", _) ->
      Value.Function(fun (Value.Tuple [Value.ImplicitsComonad(v1, d1); Value.ImplicitsComonad(v2, d2)] | Fail"Expected tuple of comonads" (v1,v2,d1,d2)) ->
        let m = d1 |> Map.toList |> List.fold (fun m (k, v) -> Map.add k v m) d2
        Value.ImplicitsComonad(Value.Tuple [v1; v2], m) ) |> Some

  | Expr.Builtin("duplicate", [_]) ->
      Value.Function(fun (Value.ImplicitsComonad(v, d) | Fail "Expected comonad with tuple" (v,d)) -> 
        Value.ImplicitsComonad(Value.Tuple [v; v], d) ) |> Some

  | Expr.Builtin("counit", _) ->
      Value.Function(fun (Value.ImplicitsComonad(v, _) | Fail "Expected comonad value" v) -> v ) |> Some

  | Expr.Builtin("cobind", [r; s]) ->
      Value.Function(fun (Value.Function(f) | Fail "Expected function" f) ->
        Value.Function(fun (Value.ImplicitsComonad(v, d) | Fail "Expected comonad" (v, d)) ->
          let r, s = Solver.ImplicitParams.evalCoeffect Map.empty r, Solver.ImplicitParams.evalCoeffect Map.empty s
          let a = f (Value.ImplicitsComonad(v, restrict d r))
          Value.ImplicitsComonad(a, restrict d s))) |> Some

  | Expr.Builtin("letimpl", [Coeffect.ImplicitParam(n, _); _; _]) ->
      Value.Function(fun (Value.Tuple [Value.ImplicitsComonad(c, d); v] | Fail "Expected tuple with implicit comonad" (c,d,v) ) ->
        Value.ImplicitsComonad(c, Map.add n v d) ) |> Some
   
  | Expr.Builtin("split", [r; s]) ->
      Value.Function(fun (Value.ImplicitsComonad(Value.Tuple [v1; v2], d) | Fail "Expected comonad of tuple" (v1,v2,d)) ->
        let r, s = Solver.ImplicitParams.evalCoeffect Map.empty r, Solver.ImplicitParams.evalCoeffect Map.empty s
        Value.Tuple [Value.ImplicitsComonad(v1, restrict d r); Value.ImplicitsComonad(v1, restrict d s)] ) |> Some

  | Expr.Builtin("lookup", [Coeffect.ImplicitParam(n, _)]) -> 
      Value.Function(fun (ImplicitsComonad(_, d) | Fail "Expected comonad value" d) -> d.[n]) |> Some

  | _ -> None

let rec skip n l = 
  match n, l with
  | 0, l -> l
  | n, x::xs -> skip (n-1) xs
  | _ -> failwith "Not enough elements"

let take n (l:'a list) = 
  let rec loop acc n (l:'a list) =
    match n, l with
    | 0, _ -> List.rev acc
    | n, x::xs -> loop (x::acc) (n-1) xs
    | _ -> failwith "Not enough elements"
  loop [] n l

/// Workaround for a FunScript bug
let unzip l = List.foldBack (fun (x,y) (xs,ys) -> x::xs, y::ys) l ([], [])

let evalDataflow ctx (Typed(_, expr)) = 
  match expr with
  | Expr.Builtin("merge", _) ->
      Value.Function(fun (Value.Tuple [Value.ListComonad(vs1); Value.ListComonad(vs2)] | Fail"Expected tuple of comonads" (vs1,vs2)) ->
        Value.ListComonad(List.map2 (fun v1 v2 -> Value.Tuple [v1; v2]) vs1 vs2) ) |> Some

  | Expr.Builtin("duplicate", [_]) ->
      Value.Function(fun (Value.ListComonad(vs) | Fail "Expected comonad with tuple" (vs)) -> 
        Value.ListComonad(List.map (fun v -> Value.Tuple [v; v]) vs) ) |> Some

  | Expr.Builtin("counit", _) ->
      Value.Function(fun (Value.ListComonad [v] | Fail "Expected comonad value" v) -> v ) |> Some

  | Expr.Builtin("cobind", [r; s]) ->
      Value.Function(fun (Value.Function(f) | Fail "Expected function" f) ->
        Value.Function(fun (Value.ListComonad(vs) | Fail "Expected comonad" vs) ->
          let r, s = Solver.Dataflow.evalCoeffect Map.empty r, Solver.Dataflow.evalCoeffect Map.empty s
          Value.ListComonad
            [ for i in 0 .. s ->
                vs |> skip i |> take (r+1) |> Value.ListComonad |> f ])) |> Some

  | Expr.Builtin("split", [r; s]) ->
      Value.Function(fun (Value.ListComonad(vs) | Fail "Expected comonad of tuple" vs) ->
        let a, b = vs |> List.map (fun (Value.Tuple[a;b] | Fail "Expected tuple" (a,b)) -> a, b) |> unzip
        let r, s = Solver.Dataflow.evalCoeffect Map.empty r, Solver.Dataflow.evalCoeffect Map.empty s
        Value.Tuple [Value.ListComonad(take (r+1) a); Value.ListComonad(take (s+1) b)] ) |> Some

  | Expr.Builtin("prev", _) ->
      Value.Function(fun (Value.ListComonad vs | Fail "Expected list comonad" (vs) ) ->
        Value.ListComonad(List.tail vs) ) |> Some
   
  | _ -> None

let rec evalPrimitive ctx (Typed(_, expr)) =
  match expr with
  | Expr.Binary(op, l, r) ->
      let op = match operators.TryFind op with Some(o) -> o | _ -> failwith "Unexpected operator"
      match eval ctx l, eval ctx r with
      | Value.Integer l, Value.Integer r -> Value.Integer(op l r)
      | _ -> failwith "Expected two numbers"

  | Expr.Tuple(args) ->
      Value.Tuple(List.map (eval ctx) args)

  | Expr.Let(pat, arg, body) ->
      eval { ctx with Variables = bind (eval ctx arg) pat ctx.Variables } body

  | Expr.App(e1, e2) ->
      match eval ctx e1, eval ctx e2 with
      | Value.Function f, v -> f v
      | _ -> failwith "Expected function"

  | Expr.Fun(pat, body) ->
      Value.Function(fun v ->
        eval { ctx with Variables = bind v pat ctx.Variables } body)

  | Expr.Builtin(("fst" | "snd") as op, _) ->
      Value.Function(fun v ->
        match v with
        | Value.Tuple [v1; v2] -> if op = "fst" then v1 else v2
        | _ -> failwith "Expected two-element tuple")

  | Expr.Var(v) -> Map.find v ctx.Variables
  | Expr.Builtin("input", _) -> Map.find "input" ctx.Variables
  | Expr.Integer n -> Value.Integer n
  //| e -> failwithf "%A" e
  | _ -> failwith "Eval failed"

and eval ctx expr =
  let special = 
    match ctx.Kind with
    | CoeffectKind.ImplicitParams -> evalImplicits ctx expr 
    | CoeffectKind.PastValues -> evalDataflow ctx expr 
    | _ -> failwith "Can only eval imploicits or past values"
  match special with
  | None -> evalPrimitive ctx expr
  | Some v -> v


