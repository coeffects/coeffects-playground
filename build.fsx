// --------------------------------------------------------------------------------------
// Generates the playground in `output` folder and hosts it with background watcher
// --------------------------------------------------------------------------------------

#load "packages/FSharp.Formatting/FSharp.Formatting.fsx"
#r "packages/FAKE/tools/FakeLib.dll"
#r "packages/Suave/lib/net40/Suave.dll"

open Fake
open Suave
open System
open System.IO
open System.Text
open Suave
open Suave.Web
open Suave.Http

// --------------------------------------------------------------------------------------
// Generating the web site
// --------------------------------------------------------------------------------------

Environment.CurrentDirectory <- __SOURCE_DIRECTORY__

/// Generates the javascript file by invoking `fsi translate.fsx`
let generateScript () =
  trace "Translating to JavaScript"
  let _, res = FSIHelper.executeFSI __SOURCE_DIRECTORY__ "translate.fsx" []
  for line in res do
    if line.IsError then traceError line.Message
    else printfn "%s" line.Message

/// Generates the `index.html` file (by translating Markdown blocks)
let processIndex () = 
  trace "Generating index file"
  let fi = File.ReadAllText("content/index.html")
  let reg = RegularExpressions.Regex(">>>>(.*?)<<<<", RegularExpressions.RegexOptions.Singleline)
  let counter = ref 0
  let output = reg.Replace(fi,RegularExpressions.MatchEvaluator(fun m -> 
    let md = m.Groups.[1].Value.Split [|'\n'|]
    let drop = md |> Seq.filter (System.String.IsNullOrWhiteSpace >> not) |> Seq.map (Seq.takeWhile ((=) ' ') >> Seq.length) |> Seq.min
    let md = md |> Seq.map (fun s -> if System.String.IsNullOrWhiteSpace s then s else s.Substring(drop)) |> String.concat "\n"
    let doc = FSharp.Literate.Literate.ParseMarkdownString(md)
    incr counter
    FSharp.Literate.Literate.WriteHtml(doc, prefix=sprintf "s%d" counter.Value, lineNumbers=false) ))
  File.WriteAllText("output/index.html", output)

/// Copies static CSS and JS files to output
let copyFiles () =
  trace "Copying static files"
  !!"web/*" |> CopyFiles "output"


// --------------------------------------------------------------------------------------
// FAKE targets
// --------------------------------------------------------------------------------------

Target "generate" (fun _ ->
  CleanDir "output"
  copyFiles()
  generateScript()
  processIndex()
)

Target "run" (fun _ ->
  // Start Suave & open web browser with the site
  let app = Files.browse (Path.Combine(__SOURCE_DIRECTORY__, "output"))
  let _, server = startWebServerAsync defaultConfig app
  Async.Start(server)
  System.Diagnostics.Process.Start("http://localhost:8083/index.html") |> ignore

  // Watch for changes & reload when app.fsx changes
  use watcher1 = 
    { BaseDirectory = __SOURCE_DIRECTORY__; Includes = [ "**/*.fs*" ]; Excludes = [] }
    |> WatchChanges (fun _ -> generateScript())
  use watcher2 = 
    { BaseDirectory = __SOURCE_DIRECTORY__; Includes = [ "**/web/*" ]; Excludes = [] }
    |> WatchChanges (fun _ -> copyFiles ())
  use watcher3 = 
    { BaseDirectory = __SOURCE_DIRECTORY__; Includes = [ "**/content/*" ]; Excludes = [] }
    |> WatchChanges (fun _ -> processIndex ())
  traceImportant "Waiting for app.fsx edits. Press any key to stop."
  System.Console.ReadLine() |> ignore
)

"generate" ==> "run"
RunTargetOrDefault "run"
