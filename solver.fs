// ------------------------------------------------------------------------------------------------
// Constraint solver - standard type equality and also coeffects
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Solver
open Coeffects
open Coeffects.Ast

/// Solve type equality constraints and produce assignments for type variables.
/// Also produce equality constraints between coeffects appearing in functions
let rec solve constraints assigns cequals =
  match constraints with
  | [] -> assigns, cequals
  | (other, Type.Variable v)::rest
  | (Type.Variable v, other)::rest ->
      match Map.tryFind v assigns with
      | Some(found) -> solve ((other, found)::rest) assigns cequals
      | None -> solve rest (Map.add v other assigns) cequals
  | (l, r)::rest when l = r -> solve rest assigns cequals
  | (Type.Func(c1, l1, r1), Type.Func(c2, l2, r2))::rest ->
      solve ((l1, l2)::(r1, r2)::rest) assigns ((c1, c2)::cequals)
  | (t1, t2)::_ ->
      failwith "Cannot unify types"

/// Replace solved type variables with the assigned types
/// (and also transform coeffects using the given function)
let rec normalize evalc solutions typ =
  match typ with 
  | Type.Variable s -> 
      match Map.tryFind s solutions with
      | Some t -> normalize evalc solutions t
      | None -> Type.Variable s
  | Type.Primitive s -> typ
  | Type.Func(c, l, r) -> Type.Func(evalc c, normalize evalc solutions l, normalize evalc solutions r)

// ------------------------------------------------------------------------------------------------
// Constraint solver for implicit parameters
// ------------------------------------------------------------------------------------------------

/// Finds the fixed point of a given function (using the default
/// equality and using loop for better JavaScript translation)
let fixedPoint f (initial:Map<string, Set<string>>) = 
  let mutable oldState = initial
  let mutable newState = f initial
  while oldState <> newState do
    let s = f newState
    oldState <- newState
    newState <- s
  newState


/// Calculate the set of implicit parameters represented by a coeffect
let rec evalCoeffect assigns coeff =
  match coeff with 
  | Coeffect.Use
  | Coeffect.Ignore -> Set.empty
  | Coeffect.ImplicitParam(s, _) -> set [s]
  | Coeffect.Merge(c1, c2)
  | Coeffect.Split(c1, c2)
  | Coeffect.Seq(c1, c2) -> Set.union (evalCoeffect assigns c1) (evalCoeffect assigns c2)
  | Coeffect.Variable s -> defaultArg (Map.tryFind s assigns) Set.empty


/// Solve coeffect constraints for implict parameters. Start with empty set for each parameter,
/// iteratively adapt the assignments using the generated constraints (and using implicit 
/// parameter-specific tricks)
let rec solveImplicits constrs =
  Map.empty |> fixedPoint (fun assigns ->
    let rec loop assigns constrs =
      match constrs with
      | (Coeffect.Variable v1, Coeffect.Variable v2)::rest -> 
          // From equalities between function types - assign union to both variables
          let v1c = evalCoeffect assigns (Coeffect.Variable v1)
          let v2c = evalCoeffect assigns (Coeffect.Variable v2)
          let cs = Set.union v1c v2c
          loop (Map.add v2 cs (Map.add v1 cs assigns)) rest
          
      | (Coeffect.Variable v, r)::rest -> 
          // Type checker keeps implicit parameters that are in lexical scope and
          // generates constraint for coeffects on the declaration-side of 'fun'
          let vc = evalCoeffect assigns (Coeffect.Variable v)
          let rc = evalCoeffect assigns r
          loop (Map.add v (Set.union vc rc) assigns) rest

      | (Coeffect.Merge(Coeffect.Variable lv, Coeffect.Variable rv), r)::rest ->
          // Generated from lambda - we place all additional implicit parameters
          // on the call-side (excluding those available in declaration-side)
          let lv = evalCoeffect assigns (Coeffect.Variable lv)
          loop (Map.add rv ((evalCoeffect assigns r) - lv) assigns) rest

      | (Coeffect.Split(Coeffect.ImplicitParam(p, _), Coeffect.Variable v), r)::rest ->
          // Generated from `let ?x = ..` - variable will be all implicits excluding `p`
          let rc = evalCoeffect assigns r
          loop (Map.add v (rc - set[p]) assigns) rest

      | [] -> assigns
      | _ -> failwith "Invalid constraint"
            
    loop assigns constrs)

