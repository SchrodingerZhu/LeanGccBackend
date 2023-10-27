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

def main (args: List String) : IO Unit := do
  if args.length < 2 then do
    IO.println "too few arguments"
  else do
    Lean.initSearchPath  (← Lean.findSysroot)
    let inputPath := args[0]!
    let outputPath := args[1]!
    let src ← IO.FS.readFile inputPath
    let dumpGimple := match ← IO.getEnv "DUMP_GIMPLE" with
      | some "true" => true
      | _ => false
    let (env, _) ← Lean.Elab.runFrontend src { } inputPath `Main
    GccJit.emitGccJit env `Main outputPath { dumpGimple }
