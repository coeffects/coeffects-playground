// ------------------------------------------------------------------------------------------------
// Constraint solver - standard type equality and also coeffects
// ------------------------------------------------------------------------------------------------

[<ReflectedDefinition>]
module Coeffects.Solver
open Coeffects
open Coeffects.Ast

let substitute v1 other = 
  let rec substituteCoeff c =
    match c with
    | Coeffect.Split(c1, c2) -> Coeffect.Split(substituteCoeff c1, substituteCoeff c2)
    | Coeffect.Merge(c1, c2) -> Coeffect.Merge(substituteCoeff c1, substituteCoeff c2)
    | Coeffect.Seq(c1, c2) -> Coeffect.Seq(substituteCoeff c1, substituteCoeff c2)
    | Coeffect.ImplicitParam(n, t) -> Coeffect.ImplicitParam(n, substitute t)
    | c -> c
  and substitute t = 
    match t with 
    | Type.Variable v2 when v1 = v2 -> other
    | Type.Variable v2 -> Type.Variable v2
    | Type.FlatComonad(c, t) -> Type.FlatComonad(substituteCoeff c, substitute t)
    | Type.Func((c1, c2), t1, t2) -> Type.Func((substituteCoeff c1, substituteCoeff c2), substitute t1, substitute t2)
    | Type.StructuralComonad(c, t) -> Type.StructuralComonad(List.map substituteCoeff c, substitute t)
    | Type.Tuple(ts) -> Type.Tuple(List.map substitute ts)
    | Type.Primitive p -> Type.Primitive p
  List.map (fun (t1, t2) -> substitute t1, substitute t2)

/// Solve type equality constraints and produce assignments for type variables.
/// Also produce equality constraints between coeffects appearing in functions
let rec solve constraints assigns cequals =
  let step (constraints, assigns, cequals) = 
    match constraints with
    | [] -> Choice1Of2(assigns, cequals)
    | (l, r)::rest when l = r -> Choice2Of2(rest, assigns, cequals)
    | (Type.Func((cf1,cs1), l1, r1), Type.Func((cf2,cs2), l2, r2))::rest ->
        Choice2Of2((l1, l2)::(r1, r2)::rest, assigns, (cf1, cf2)::(cs1, cs2)::cequals)
    | (Type.Tuple(ls), Type.Tuple(rs))::rest when List.length ls = List.length rs ->
        Choice2Of2((List.zip ls rs) @ rest, assigns, cequals)
    | (Type.FlatComonad(c1, t1), Type.FlatComonad(c2, t2))::rest ->
        Choice2Of2((t1,t2) :: rest, assigns, (c1, c2)::cequals)
    | (Type.StructuralComonad(c1, t1), Type.StructuralComonad(c2, t2))::rest when List.length c1 = List.length c2 ->
        Choice2Of2((t1,t2) :: rest, assigns, List.zip c1 c2 @ cequals)
    | (other, Type.Variable v)::rest
    | (Type.Variable v, other)::rest ->
        match Map.tryFind v assigns with
        | Some(found) -> Choice2Of2((other, found)::rest, assigns, cequals)
        | None -> Choice2Of2(substitute v other rest,Map.add v other assigns, cequals)
    | (t1, t2)::_ ->
        Errors.typeMismatch t1 t2

  let mutable result = None
  let mutable state = constraints, assigns, cequals
  while Option.isNone result do
    match step state with
    | Choice1Of2 r -> result <- Some r
    | Choice2Of2 s -> state <- s
  result.Value

/// Replace solved type variables with the assigned types
/// (and also transform coeffects using the given function)
let normalizeType evalc solutions typ =
  
  // Generate nice names for free type variables
  let variableName n = if n <= 25 then (char (97 + n)).ToString() else "a" + (string (n - 26))
  let renamedVars = ref Map.empty
  let getVariableMapping (s:string) = 
    match Map.tryFind s renamedVars.Value with
    | Some s -> s
    | None -> 
        renamedVars.Value <- Map.add s (variableName renamedVars.Value.Count) renamedVars.Value
        renamedVars.Value.[s]

  // Recursively normalize the type
  let rec loop evalc solutions typ =
    match typ with 
    | Type.FlatComonad(c, t) -> 
        Type.FlatComonad(evalc c, loop evalc solutions t)
    | Type.StructuralComonad(c, t) -> 
        Type.StructuralComonad(List.map evalc c, loop evalc solutions t)
    | Type.Variable s -> 
        match Map.tryFind s solutions with
        | Some t -> loop evalc solutions t
        | None -> Type.Variable (getVariableMapping s)
    | Type.Tuple(ts) ->
        Type.Tuple(List.map (loop evalc solutions) ts)
    | Type.Primitive s -> typ
    | Type.Func((cf, cs), l, r) -> 
        Type.Func((evalc cf, evalc cs), loop evalc solutions l, loop evalc solutions r)
  loop evalc solutions typ 

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

/// Remove element satisfying the given condition from a list
let rec remove f list = 
  match list with 
  | [] -> None, []
  | x::xs when f x -> Some x, xs
  | x::xs ->
      let a, b = remove f xs
      a, x::b

/// Build equivalence classes between variables. Returns a function that takes a variable, value & 
/// map and adds an assignment for all variables that are equivalent to the given variable
let buildEquivalenceClasses vars =
  let rec loop (acc:list<Set<string>>) sets =
    match sets with 
    | first::sets ->
        // If there is set that overlaps with the current one, union them
        let opt, sets = remove (fun second -> Set.count (Set.intersect first second) > 0) sets 
        let acc = 
          match opt with 
          | None -> first::acc
          | Some other -> (Set.union first other)::acc
        loop acc sets 
    | [] -> acc
                
  let equivVars = vars |> List.map (fun (v1, v2) -> set[v1; v2]) |> fixedPoint (loop [] >> List.sort)

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
    | Coeffect.None -> Errors.unexpected "Unexpected <code>Coeffect.None</code> in implicit parameter coeffects in <code>evalCoeffect</code>."
    | Coeffect.Past _ -> Errors.unexpected "Unexpected <code>Coeffect.Past</code> in implicit parameter coeffects in <code>evalCoeffect</code>."

  /// Solve coeffect constraints for implict parameters. Start with empty set for each parameter,
  /// iteratively adapt the assignments using the generated constraints (and using implicit 
  /// parameter-specific tricks)
  let solve constrs =
    Trace.log "*** Solving implicit params coeffect constraints ***"
    for c1, c2 in constrs do
      Trace.log [| Trace.formatCoeffect c1; Trace.formatCoeffect c2 |]

    // Turn equality between variables into equivalence classes & filter out the constraints
    // Also drop all 'None' coeffects, which are to be ignored 
    let equivVars = constrs |> List.choose (function 
        Coeffect.Variable v1, Coeffect.Variable v2 -> Some(v1, v2) | _ -> None)
    let constrs = constrs |> List.filter (function
        Coeffect.None, _ | _, Coeffect.None |
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
        | (c1, c2)::_ -> Errors.invalidConstraint "Cannot solve implicit parameter constraints." c1 c2
            
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
    | Coeffect.ImplicitParam _ -> Errors.unexpected "Unexpected <code>Coeffect.ImplicitParam</code> in dataflow coeffects in <code>evalCoeffect</code>."    
    | Coeffect.None -> Errors.unexpected "Unexpected <code>Coeffect.None</code> in implicit parameter coeffects in <code>evalCoeffect</code>."
    | _ -> Errors.unexpected "Unexpected coeffect value in implicit parameter coeffects in <code>evalCoeffect</code>."


  /// Solve coeffect constraints for data-flow. Start with 0 for all variables and
  /// keep recalculating them until a fixed point is reached.
  let solve constrs  =
    Trace.log "*** Solving dataflow coeffect constraints ***"
    for c1, c2 in constrs do
      Trace.log [| Trace.formatCoeffect c1; Trace.formatCoeffect c2 |]

    // Turn equality between variables into equivalence classes
    // Turn 'merge(r, s) = X' constraints from 'fun' into equivalence 
    //   'r = s' and replace them with simple 'r = X'
    // Also, filter out all constraints involving `None` coeffects
    let equivVars = constrs |> List.collect (function 
      | Coeffect.Merge(Coeffect.Variable v1, Coeffect.Variable v2), Coeffect.Variable v3 -> [v1, v2; v1, v3]
      | Coeffect.Merge(Coeffect.Variable v1, Coeffect.Variable v2), _ 
      | Coeffect.Variable v1, Coeffect.Variable v2 -> [v1, v2] 
      | _ -> [])
    let constrs = constrs |> List.choose (function
      | Coeffect.None, _ | _, Coeffect.None
      | Coeffect.Variable _, Coeffect.Variable _ -> None 
      | Coeffect.Merge(Coeffect.Variable v1, Coeffect.Variable v2), r ->
          Some(Coeffect.Variable v1, r)
      | t -> Some t)
    let addAssignment : string -> int -> _ = buildEquivalenceClasses equivVars

    // All remaining constraints have the form "v = ..." and so this is easy
    Map.empty |> fixedPoint (fun assigns ->    
      let rec loop (assigns:Map<string,int>) constrs =
        match constrs with
        | (r, Coeffect.Variable v)::rest
        | (Coeffect.Variable v, r)::rest -> 
            let n = evalCoeffect assigns r
            loop (addAssignment v n assigns) rest
        | [] -> assigns
        | (c1, c2)::_ -> Errors.invalidConstraint "Cannot solve dataflow constraints." c1 c2
      loop assigns constrs)
  
