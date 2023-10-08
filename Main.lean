import «LeanGccBackend»
import «LeanGccBackend».Basic
import «LeanGccBackend».Runtime
import «LeanGccBackend».Codegen
import «LeanGccJit»

open Lean.IR
open LeanGccJit.Core

def main : IO Unit := do 
  let ctx ← Context.acquire
  let context : GccJit.GccContext := {
    env := {
      const2ModIdx := default,
      constants := default,
      extensions := default,
      extraConstNames := default,
    }
    modName := "test"
    ctx
  }
  let state : GccJit.State := default 
  ctx.setIntOption IntOption.OptimizationLevel 3
  let ops := do
    GccJit.populateRuntimeTable
    GccJit.emitMainFn
  
  let _ ← ops.run state context
  -- let _ ← GccJit.getLeanDecRef.run state context
  -- let _ ← GccJit.getLeanIncN.run state context
  ctx.setBoolOption BoolOption.DumpInitialGimple true
  ctx.compileToFile OutputKind.ObjectFile "/tmp/test.o"
  ctx.release
