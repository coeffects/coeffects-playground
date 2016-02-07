// ------------------------------------------------------------------------------------------------
// Error reporting and logging
// ------------------------------------------------------------------------------------------------

namespace Coeffects
open Coeffects.Ast

module TraceInternal = 
  /// Log object to browser console or to console
  [<FunScript.JSEmitInline("console.log({0})")>]
  let log obj = printfn "%A" obj

[<ReflectedDefinition>]
module Trace = 
  let traceEnabled = false

  /// Log user interaction or other event 
  [<FunScript.JSEmit("var o = {}; {0}.forEach(function(tup) { o[tup.Items[0]] = tup.Items[1]; }); return o;")>]
  let data (args:(string*string)[]) = failwith "!"

  /// Log user interaction or other event 
  [<FunScript.JSEmitInline("logEvent({0}, {1}, {2})")>]
  let event category event data = failwith "!"

  /// If `traceEnabled` is set, logs object to browser console
  /// or to console output (in browser, it shows expandable object)
  let log obj = 
    if traceEnabled then 
      TraceInternal.log obj

  /// Format coeffect as simple string
  let rec formatCoeffect = function
    | Coeffect.Variable s -> "'" + s
    | Coeffect.Use -> "use"
    | Coeffect.Ignore -> "ignore"
    | Coeffect.Merge(l, r) -> "merge(" + formatCoeffect l + "," + formatCoeffect r + ")"
    | Coeffect.Split(l, r) -> "split(" + formatCoeffect l + "," + formatCoeffect r + ")"
    | Coeffect.Seq(l, r) -> "seq(" + formatCoeffect l + "," + formatCoeffect r + ")"
    | Coeffect.None -> "none"
    | Coeffect.Past n -> "past(" + string n + ")"
    | Coeffect.ImplicitParam(s, _) -> "?" + s

  /// Format type as HTML-compatible string
  let rec formatType = function 
    | Type.FlatComonad(c, t) -> "C " + formatCoeffect c + " " + formatType t
    | Type.StructuralComonad(cs, t) -> "C [" + (List.map formatCoeffect cs |> String.concat ", ") + "] " + formatType t
    | Type.Func(_, t1, t2) -> "(" + formatType t1 + " -&gt; " + formatType t2 + ")"
    | Type.Primitive t -> t
    | Type.Tuple(tys) -> "(" + (String.concat " * " (List.map formatType tys)) + ")"
    | Type.Variable v -> "'" + v


[<ReflectedDefinition>]
module Errors =
  open Trace

  let unexpected s = failwith ("<strong>Unexpected error.</strong><br /> This should not normally happen. " + s + " Please <a href='https://github.com/tpetricek/Coeffects.Playground/issues/new'>report an issue</a>.")
  let syntaxError s = failwith ("<strong>Syntax error.</strong><br /> We cannot handle this source code. " + s)
  let typeMismatch (t1:Type) (t2:Type) = failwith ("<strong>Type mismatch.</strong><br /> Cannot unify type <code>" + formatType t1 + "</code> with type <code>" + formatType t2 + "</code>.")
  let invalidConstraint s (c1:Coeffect) (c2:Coeffect) = failwith ("<strong>Invalid constraint.</strong><br /> " + s + " Attempting to unify <code>" + (formatCoeffect c1) + "</code> and <code>" + (formatCoeffect c2) + "</code>.")
  let invalidCoeffect s (c:Coeffect) = failwith ("<strong>Invalid coeffect.</strong><br /> " + s + " Coeffect value was <code>" + formatCoeffect c + "</code>.")
  let evaluationFailed s = failwith ("<strong>Evaluation failed.</strong><br /> This should not normally happen. " + s + " Please <a href='https://github.com/tpetricek/Coeffects.Playground/issues/new'>report an issue</a>.")
  let parseError s = failwith ("<strong>Parsing error.</strong><br /> " + s)