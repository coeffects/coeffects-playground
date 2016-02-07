#r "packages/Suave/lib/net40/Suave.dll"
#r "packages/FunScript/lib/net40/FunScript.dll"
#r "packages/FunScript/lib/net40/FunScript.Interop.dll"
#r "packages/FunScript.TypeScript.Binding.lib/lib/net40/FunScript.TypeScript.Binding.lib.dll"
#r "packages/FunScript.TypeScript.Binding.jquery/lib/net40/FunScript.TypeScript.Binding.jquery.dll"

open System.IO
open FunScript
open FunScript.Compiler

#load "parsec.fs"
#load "ast.fs"
#load "errors.fs"
#load "lexer.fs"
#load "parser.fs"
#load "solver.fs"
#load "typechecker.fs"
#load "pretty.fs"
#load "translation.fs"
#load "evaluation.fs"
#load "gui.fs"

open FunScript.TypeScript

// ------------------------------------------------------------------------------------------------
// Translating F# code to JavaScript using FunScript
// ------------------------------------------------------------------------------------------------

[<JSEmitInline("{0}.join('')")>]
let newString(c:char[]) : string = failwith "!"

let replacer = 
  ExpressionReplacer.createUnsafe 
    <@ fun (c:char[]) -> new System.String(c) @> <@ fun c -> newString c @>

let translate q = Compiler.Compile(q, fun l -> replacer :: l)

let script = 
  translate <@ Coeffects.Gui.main() @>
  |> sprintf "$(function() { %s })"

File.WriteAllText(__SOURCE_DIRECTORY__ + "/output/script.js", script)