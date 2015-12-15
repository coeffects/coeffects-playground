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
let rec normalizeType evalc solutions typ =
  match typ with 
  | Type.Variable s -> 
      match Map.tryFind s solutions with
      | Some t -> normalizeType evalc solutions t
      | None -> Type.Variable s
  | Type.Primitive s -> typ
  | Type.Func(c, l, r) -> 
      Type.Func(evalc c, normalizeType evalc solutions l, normalizeType evalc solutions r)

// ------------------------------------------------------------------------------------------------
// Utilities for constraint solving
// ------------------------------------------------------------------------------------------------

/// Finds the fixed point of a given function (using the default
/// equality and using loop for better JavaScript translation)
let fixedPoint f initial = 
  let mutable oldState = initial
  let mutable newState = f initial
  while oldState <> newState do
    let s = f newState
    oldState <- newState
    newState <- s
  newState

/// Build equivalence classes between variables. Returns a function that takes a variable, value & 
/// map and adds an assignment for all variables that are equivalent to the given variable
let buildEquivalenceClasses vars =
  let rec collectEquals groups (constrs:list<string * string>) = 
    match constrs with
    | (v1, v2)::rest ->
        let found, groups = groups |> List.fold (fun (found, groups) group -> 
          if found then 
            found, group::groups
          elif Set.contains v1 group || Set.contains v2 group then
            true, (Set.add v1 (Set.add v2 group))::groups
          else
            false, group::groups) (false, [])
        let groups = if found then groups else (set [v1; v2])::groups
        collectEquals groups rest
    | [] -> groups

  let equivVars = collectEquals [] vars

  // Adds assignment for all variables that are equivalent to 'v'
  fun v (value:'T) map ->
    let group = equivVars |> List.tryFind (Set.contains v) |> Option.map Set.toList
    let group = defaultArg group [v]
    group |> List.fold (fun map v -> Map.add v value map) map


// ------------------------------------------------------------------------------------------------
// Constraint solver for implicit parameters
// ------------------------------------------------------------------------------------------------

module ImplicitParams = 

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
    | Coeffect.Past _ -> failwith "Unexpected past in implicit parameter coeffects"

  /// Solve coeffect constraints for implict parameters. Start with empty set for each parameter,
  /// iteratively adapt the assignments using the generated constraints (and using implicit 
  /// parameter-specific tricks)
  let solve constrs =

    // Turn equality between variables into equivalence classes & filter out the constraints
    let equivVars = constrs |> List.choose (function 
        Coeffect.Variable v1, Coeffect.Variable v2 -> Some(v1, v2) | _ -> None)
    let constrs = constrs |> List.filter (function
        Coeffect.Variable _, Coeffect.Variable _ -> false | _ -> true)
    let addAssignment = buildEquivalenceClasses equivVars

    // Calculate the fixed point of the solution-updating function
    Map.empty |> fixedPoint (fun assigns ->    

      let rec loop assigns constrs =
        match constrs with
        | (Coeffect.Variable v, r)::rest -> 
            // Type checker keeps implicit parameters that are in lexical scope and
            // generates constraint for coeffects on the declaration-side of 'fun'
            let vc = evalCoeffect assigns (Coeffect.Variable v)
            let rc = evalCoeffect assigns r
            loop (addAssignment v (Set.union vc rc) assigns) rest

        | (Coeffect.Merge(Coeffect.Variable lv, Coeffect.Variable rv), r)::rest ->
            // Generated from lambda - we place all additional implicit parameters
            // on the call-side (excluding those available in declaration-side)
            let lv = evalCoeffect assigns (Coeffect.Variable lv)
            loop (addAssignment rv ((evalCoeffect assigns r) - lv) assigns) rest

        | (Coeffect.Split(Coeffect.ImplicitParam(p, _), Coeffect.Variable v), r)::rest ->
            // Generated from `let ?x = ..` - variable will be all implicits excluding `p`
            let rc = evalCoeffect assigns r
            loop (addAssignment v (rc - set[p]) assigns) rest

        | [] -> assigns
        | _ -> failwith "Invalid constraint"
            
      loop assigns constrs)

// ------------------------------------------------------------------------------------------------
// Constraint solver for data-flow
// ------------------------------------------------------------------------------------------------

module Dataflow = 
  /// Helper for let binding
  let (|Let|) a x = a, x

  /// Evaluate current value assinged to a variable, using 0 when variable has no assignment
  let rec evalCoeffect assigns coeff = 
    match coeff with
    | Coeffect.Ignore | Coeffect.Use -> 0  
    | Let min (op, Coeffect.Merge(c1, c2))
    | Let max (op, Coeffect.Split(c1, c2))
    | Let (+) (op, Coeffect.Seq(c1, c2)) -> op (evalCoeffect assigns c1) (evalCoeffect assigns c2)
    | Coeffect.Past(n) -> n
    | Coeffect.Variable v -> defaultArg (Map.tryFind v assigns) 0
    | Coeffect.ImplicitParam _ -> failwith "Unexpected implicit param value in coeffect"
    | _ -> failwith "Unexpected coeffect value"


  /// Solve coeffect constraints for data-flow. Start with 0 for all variables and
  /// keep recalculating them until a fixed point is reached.
  let solve constrs  =

    // Turn equality between variables into equivalence classes
    // Turn 'merge(r, s) = X' constraints from 'fun' into equivalence 
    //   'r = s' and replace them with simple 'r = X'
    let equivVars = constrs |> List.choose (function 
      | Coeffect.Merge(Coeffect.Variable v1, Coeffect.Variable v2), _ 
      | Coeffect.Variable v1, Coeffect.Variable v2 -> Some(v1, v2) | _ -> None)
    let constrs = constrs |> List.choose (function
      | Coeffect.Variable _, Coeffect.Variable _ -> None 
      | Coeffect.Merge(Coeffect.Variable v1, Coeffect.Variable v2), r ->
          Some(Coeffect.Variable v1, r)
      | t -> Some t)
    let addAssignment : string -> int -> _ = buildEquivalenceClasses equivVars

    // All remaining constraints have the form "v = ..." and so this is easy
    Map.empty |> fixedPoint (fun assigns ->    
      let rec loop (assigns:Map<string,int>) constrs =
        match constrs with
        | (Coeffect.Variable v, r)::rest -> 
            let n = evalCoeffect assigns r
            loop (addAssignment v n assigns) rest
        | [] -> assigns
        | _ -> failwith "Invalid constraint"            
      loop assigns constrs)
  
