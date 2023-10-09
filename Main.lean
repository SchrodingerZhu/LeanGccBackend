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

def src := "def main (args : List String) : IO Unit := 
  if args.isEmpty then
    IO.println \"Hello, world!\"
  else
    IO.println s!\"{100000000000000000000000000000000000000000000000}\""

def main : IO Unit := do 
  Lean.initSearchPath  (← Lean.findSysroot)
  let (env, x) ← Lean.Elab.runFrontend src {} "test.lean" `Main
  GccJit.emitGccJit env `Main "/tmp/test.o"
  -- let ctx ← Context.acquire
  -- let context : GccJit.GccContext := {
  --   env := {
  --     const2ModIdx := default,
  --     constants := default,
  --     extensions := default,
  --     extraConstNames := default,
  --   }
  --   modName := "test"
  --   ctx
  -- }
  -- let state : GccJit.State := default 
  -- ctx.setIntOption IntOption.OptimizationLevel 3
  -- let ops := do
  --   GccJit.populateRuntimeTable
  --   GccJit.emitMainFn
  
  -- let _ ← ops.run state context
  -- -- let _ ← GccJit.getLeanDecRef.run state context
  -- -- let _ ← GccJit.getLeanIncN.run state context
  -- ctx.setBoolOption BoolOption.DumpInitialGimple true
  -- ctx.compileToFile OutputKind.ObjectFile "/tmp/test.o"
  -- ctx.release
