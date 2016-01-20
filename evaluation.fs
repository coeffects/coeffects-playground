// ------------------------------------------------------------------------------------------------
// An interpreter that evaluates translated expressions (with comonad primitives)
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Evaluation

open Coeffects
open Coeffects.Ast

// ------------------------------------------------------------------------------------------------
// List helper functions & FunScript bug workaround for unzip
// ------------------------------------------------------------------------------------------------

let rec skip n l = 
  match n, l with
  | 0, l -> l
  | n, x::xs -> skip (n-1) xs
  | _ -> Errors.evaluationFailed "Insufficient number of elements in a list."

let take n (l:'a list) = 
  let rec loop acc n (l:'a list) =
    match n, l with
    | 0, _ -> List.rev acc
    | n, x::xs -> loop (x::acc) (n-1) xs
    | _ -> Errors.evaluationFailed "Insufficient number of elements in a list."
  loop [] n l

let unzip l = 
  List.foldBack (fun (x,y) (xs,ys) -> x::xs, y::ys) l ([], [])

// ------------------------------------------------------------------------------------------------
// Evaluation itself
// ------------------------------------------------------------------------------------------------

/// Represents values in the coeffect evaluator
type Value =
  // Standard functional language values
  | Unit
  | Number of float
  | Function of (Value -> Value)
  | Tuple of Value list
  // Comonadic values
  | ImplicitsComonad of Value * Map<string, Value>
  | ListComonad of Value list


/// Variable assignment kept as a state during the evaluation 
type EvaluationContext = 
  { Variables : Map<string, Value> 
    Kind : CoeffectKind }


/// Assign values to variables bound in a pattern & return new context
let rec bind value (TypedPat(_, pattern)) vars = 
  match pattern, value with
  | Pattern.Var n, v -> Map.add n v vars
  | Pattern.Tuple pats, Value.Tuple vals when pats.Length = vals.Length ->
      List.zip pats vals |> List.fold (fun ctx (p, v) -> bind v p ctx) vars
  | _ -> Errors.evaluationFailed "The provided value does not match the specified pattern."

let operators : Map<string, float -> float -> float> = 
  Map.ofList [ "+", (+); "-", (-); "*", (*); "/", (/); "^", ( ** ) ] 

let restrict (m:Map<string, Value>) s = 
  Map.ofList [ for v in Set.toList s -> v, Map.find v m ]

let (|Fail|) s _ = Errors.evaluationFailed s


/// Evaluate primitive operations of implicit parameter coeffect language
/// Returns `None` when the construct is not a comonadic primitive 
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

  | Expr.Builtin("cobind", [Annotation.Flat r; Annotation.Flat s]) ->
      Value.Function(fun (Value.Function(f) | Fail "Expected function" f) ->
        Value.Function(fun (Value.ImplicitsComonad(v, d) | Fail "Expected comonad" (v, d)) ->
          let r, s = Solver.ImplicitParams.evalCoeffect Map.empty r, Solver.ImplicitParams.evalCoeffect Map.empty s
          let a = f (Value.ImplicitsComonad(v, restrict d r))
          Value.ImplicitsComonad(a, restrict d s))) |> Some

  | Expr.Builtin("letimpl", [Annotation.Flat(Coeffect.ImplicitParam(n, _)); _; _]) ->
      Value.Function(fun (Value.Tuple [Value.ImplicitsComonad(c, d); v] | Fail "Expected tuple with implicit comonad" (c,d,v) ) ->
        Value.ImplicitsComonad(c, Map.add n v d) ) |> Some
   
  | Expr.Builtin("split", [Annotation.Flat r; Annotation.Flat s]) ->
      Value.Function(fun (Value.ImplicitsComonad(Value.Tuple [v1; v2], d) | Fail "Expected comonad of tuple" (v1,v2,d)) ->
        let r, s = Solver.ImplicitParams.evalCoeffect Map.empty r, Solver.ImplicitParams.evalCoeffect Map.empty s
        Value.Tuple [Value.ImplicitsComonad(v1, restrict d r); Value.ImplicitsComonad(v1, restrict d s)] ) |> Some

  | Expr.Builtin("lookup", [Annotation.Flat(Coeffect.ImplicitParam(n, _))]) -> 
      Value.Function(fun (ImplicitsComonad(_, d) | Fail "Expected comonad value" d) -> d.[n]) |> Some

  | _ -> None


/// Evaluate primitive operations of dataflow coeffect language
/// Returns `None` when the construct is not a comonadic primitive 
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

  | Expr.Builtin("cobind", [Annotation.Flat r; Annotation.Flat s]) ->
      Value.Function(fun (Value.Function(f) | Fail "Expected function" f) ->
        Value.Function(fun (Value.ListComonad(vs) | Fail "Expected comonad" vs) ->
          let r, s = Solver.Dataflow.evalCoeffect Map.empty r, Solver.Dataflow.evalCoeffect Map.empty s
          Value.ListComonad
            [ for i in 0 .. s ->
                vs |> skip i |> take (r+1) |> Value.ListComonad |> f ])) |> Some

  | Expr.Builtin("split", [Annotation.Flat r; Annotation.Flat s]) ->
      Value.Function(fun (Value.ListComonad(vs) | Fail "Expected comonad of tuple" vs) ->
        let a, b = vs |> List.map (fun (Value.Tuple[a;b] | Fail "Expected tuple" (a,b)) -> a, b) |> unzip
        let r, s = Solver.Dataflow.evalCoeffect Map.empty r, Solver.Dataflow.evalCoeffect Map.empty s
        Value.Tuple [Value.ListComonad(take (r+1) a); Value.ListComonad(take (s+1) b)] ) |> Some

  | Expr.Builtin("prev", _) ->
      Value.Function(fun (Value.ListComonad vs | Fail "Expected list comonad" (vs) ) ->
        Value.ListComonad(List.tail vs) ) |> Some
   
  | _ -> None


/// Evaluate standard functional language constructs and non-comonadic primitives.
/// Fails when the expression does not match, so this should be called as the last option.
let rec evalPrimitive ctx (Typed(_, expr)) =
  match expr with
  | Expr.Binary(op, l, r) ->
      let op = match operators.TryFind op with Some(o) -> o | _ -> Errors.evaluationFailed "Unexpected operator in binary expression."
      match eval ctx l, eval ctx r with
      | Value.Number l, Value.Number r -> Value.Number(op l r)
      | _ -> Errors.evaluationFailed "Cannot evaluate binary operation. Expected two numerical values."

  | Expr.Tuple(args) ->
      Value.Tuple(List.map (eval ctx) args)

  | Expr.Let(pat, arg, body) ->
      eval { ctx with Variables = bind (eval ctx arg) pat ctx.Variables } body

  | Expr.App(e1, e2) ->
      match eval ctx e1, eval ctx e2 with
      | Value.Function f, v -> f v
      | _ -> Errors.evaluationFailed "Cannot evaluate function application. Left-hand side is not a function!"

  | Expr.Fun(pat, body) ->
      Value.Function(fun v ->
        eval { ctx with Variables = bind v pat ctx.Variables } body)

  | Expr.Builtin(("fst" | "snd") as op, _) ->
      Value.Function(fun v ->
        match v with
        | Value.Tuple [v1; v2] -> if op = "fst" then v1 else v2
        | _ -> Errors.evaluationFailed "Cannot evaluate tuple access. Right-hand side is not a tuple!")

  | Expr.Var(v) -> 
      match Map.tryFind v ctx.Variables with
      | Some v -> v
      | _ -> Errors.evaluationFailed "Variable access failed. Variable is not in scope."

  | Expr.Builtin("input", _) -> Map.find "input" ctx.Variables
  | Expr.Number n -> Value.Number n
  | _ -> Errors.evaluationFailed "Evaluation failed. Unexpected expression."


/// Evaluate a translated expression in a coeffect programming language
and eval ctx expr =
  let special = 
    match ctx.Kind with
    | CoeffectKind.ImplicitParams -> evalImplicits ctx expr 
    | CoeffectKind.PastValues -> evalDataflow ctx expr 
    | _ -> Errors.evaluationFailed "Evaluation failed. The evaluation kind must be <code>ImplicitParams</code> or <code>PastValues</code>."
  match special with
  | None -> evalPrimitive ctx expr
  | Some v -> v


