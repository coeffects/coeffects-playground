// --------------------------------------------------------------------------------------
// A simple FAKE build script that:
//  1) Hosts Suave server locally & reloads web part that is defined in 'app.fsx'
//  2) Deploys the web application to Azure web sites when called with 'build deploy'
// --------------------------------------------------------------------------------------

#r "packages/FSharp.Compiler.Service/lib/net45/FSharp.Compiler.Service.dll"
#r "packages/Suave/lib/net40/Suave.dll"
#r "packages/FAKE/tools/FakeLib.dll"
#load "paket-files/matthid/Yaaf.FSharp.Scripting/src/source/Yaaf.FSharp.Scripting/YaafFSharpScripting.fs"

open Fake
open Suave
open System
open Suave.Web
open Suave.Types
open Yaaf.FSharp.Scripting

// --------------------------------------------------------------------------------------
// When `app.fsx` changes, we `#load "app.fsx"` using the F# Interactive service
// and then get the `App.app` value (top-level value defined using `let app = ...`).
// --------------------------------------------------------------------------------------

let internal fsiSession = ScriptHost.CreateNew()

let reloadScript () =
  try
    traceImportant "Reloading app.fsx script..."
    let appFsx = __SOURCE_DIRECTORY__ @@ "app.fsx"
    fsiSession.EvalInteraction(sprintf "#load @\"%s\"" appFsx)
    fsiSession.EvalInteraction("open App")
    Some(fsiSession.EvalExpression<WebPart>("app"))
  with :? FsiEvaluationException as e ->
    traceError "Reloading app.fsx script failed."
    traceError (sprintf "Message: %s\nError: %s" e.Message e.Result.Error.Merged)
    None

// --------------------------------------------------------------------------------------
// Suave server that redirects all request to currently loaded WebPart. We watch for
// changes & reload automatically. The WebPart is then hosted at http://localhost:8087
// --------------------------------------------------------------------------------------

let currentApp = ref (fun _ -> async { return None })

let serverConfig =
  { defaultConfig with
      homeFolder = Some __SOURCE_DIRECTORY__
      logger = Logging.Loggers.saneDefaultsFor Logging.LogLevel.Debug
      bindings = [ HttpBinding.mk' HTTP  "127.0.0.1" 8087] }

let reloadAppServer () =
  reloadScript() |> Option.iter (fun app ->
    currentApp.Value <- app
    traceImportant "New version of app.fsx loaded!" )


// --------------------------------------------------------------------------------------
// Running the site locally with automatic refresh
// --------------------------------------------------------------------------------------

Target "run" (fun _ ->
  let app ctx = currentApp.Value ctx
  let _, server = startWebServerAsync serverConfig app

  // Start Suave & open web browser with the site
  reloadAppServer()
  Async.Start(server)
  System.Diagnostics.Process.Start("http://localhost:8087") |> ignore

  // Watch for changes & reload when app.fsx changes
  let sources = { BaseDirectory = __SOURCE_DIRECTORY__; Includes = [ "**/*.fs*" ]; Excludes = [] }
  use watcher = sources |> WatchChanges (fun _ -> reloadAppServer())
  traceImportant "Waiting for app.fsx edits. Press any key to stop."
  System.Console.ReadLine() |> ignore
)

// --------------------------------------------------------------------------------------
// Targets for running build script in background (for Atom)
// --------------------------------------------------------------------------------------

open System.IO
open System.Diagnostics

let runningFileLog = __SOURCE_DIRECTORY__ @@ "build.log"
let runningFile = __SOURCE_DIRECTORY__ @@ "build.running"

Target "spawn" (fun _ ->
  if File.Exists(runningFile) then
    failwith "The build is already running!"

  let ps =
    ProcessStartInfo
      ( WorkingDirectory = __SOURCE_DIRECTORY__,
        FileName = __SOURCE_DIRECTORY__  @@ "packages/FAKE/tools/FAKE.exe",
        Arguments = "run --fsiargs build.fsx",
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false )
  use fs = new FileStream(runningFileLog, FileMode.Create, FileAccess.ReadWrite, FileShare.Read)
  use sw = new StreamWriter(fs)
  let p = Process.Start(ps)
  p.ErrorDataReceived.Add(fun data -> printfn "%s" data.Data; sw.WriteLine(data.Data); sw.Flush())
  p.OutputDataReceived.Add(fun data -> printfn "%s" data.Data; sw.WriteLine(data.Data); sw.Flush())
  p.EnableRaisingEvents <- true
  p.BeginOutputReadLine()
  p.BeginErrorReadLine()

  File.WriteAllText(runningFile, string p.Id)
  while File.Exists(runningFile) do
    System.Threading.Thread.Sleep(500)  
  p.Kill()
)

Target "attach" (fun _ ->
  if not (File.Exists(runningFile)) then
    failwith "The build is not running!"
  use fs = new FileStream(runningFileLog, FileMode.Open, FileAccess.Read, FileShare.ReadWrite)
  use sr = new StreamReader(fs)
  while File.Exists(runningFile) do
    let msg = sr.ReadLine()
    if not (String.IsNullOrEmpty(msg)) then
      printfn "%s" msg 
    else System.Threading.Thread.Sleep(500)
)

Target "stop" (fun _ ->
  if not (File.Exists(runningFile)) then
    failwith "The build is not running!"
  File.Delete(runningFile)
)

// --------------------------------------------------------------------------------------
// Minimal Azure deploy script - just overwrite old files with new ones
// --------------------------------------------------------------------------------------

Target "deploy" (fun _ ->
  let sourceDirectory = __SOURCE_DIRECTORY__
  let wwwrootDirectory = __SOURCE_DIRECTORY__ @@ "../wwwroot"
  CleanDir wwwrootDirectory
  CopyRecursive sourceDirectory wwwrootDirectory false |> ignore
)

RunTargetOrDefault "run"
