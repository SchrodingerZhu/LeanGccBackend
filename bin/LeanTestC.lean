import «LeanGccBackend»
import «LeanGccBackend».Basic
import «LeanGccBackend».Runtime
import «LeanGccBackend».Codegen
import «LeanGccJit»
import Lean.Util.Path
import Lean.Elab.Frontend
open Lean.IR
open LeanGccJit.Core
open Lean.Elab.Frontend

def parseArgs (args : List String) : IO (GccJit.CodegenOptions × String × String) := do
  let mut res : GccJit.CodegenOptions := {}
  let mut expectOutput := false
  let mut input := none
  let mut output := none
  for arg in args do
    if arg.startsWith  "--gccjit-cmdopt=" then do
      let suffix := arg.drop 10
      for j in suffix.split (λ c => c == ',') do
        res := { res with gccCmdOpts := res.gccCmdOpts.push j }
    else if arg == "--gccjit-dump-gimple" then
      res := { res with dumpGimple := true }
    else if arg == "--gccjit-debug" then
      res := { res with debugInfo := true }
    else if arg.startsWith "-O" then
      res := { res with optLevel := arg.drop 2 |>.toNat?.getD 1 }
    else if arg == "-o" then
      expectOutput := true
    else if expectOutput then
      output := arg
      expectOutput := false
    else if arg.startsWith "-" then
      panic! s!"unknown option {arg}"
    else
      input := arg
  match input, output with
  | some a, some b => return (res, a, b)
  | some a , none => return (res, a, a ++ ".o")
  | none, _ => throw $ IO.userError "no input file"

def main (args: List String) : IO Unit := do
  if args.length < 2 then do
    IO.println "too few arguments"
  else do
    let args := args.toArray
    Lean.initSearchPath  (← Lean.findSysroot)
    let (options, inputPath, outputPath) ← parseArgs args.toList
    let src ← IO.FS.readFile inputPath
    let (env, _) ← Lean.Elab.runFrontend src { } inputPath `Main
    GccJit.emitGccJit env `Main outputPath options
