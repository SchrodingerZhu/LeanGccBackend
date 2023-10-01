import «LeanGccBackend»
import «LeanGccBackend».Runtime
import «LeanGccJit»

open Lean.IR
open LeanGccJit.Core

def main : IO Unit := do 
  let ctx ← Context.acquire
  let context : GccJit.GccContext := {
    modName := "test"
    ctx
  }
  let state : GccJit.State := default 
  ctx.setIntOption IntOption.OptimizationLevel 3
  -- let _ ← GccJit.getLeanIncRefN.run state context
  -- let _ ← GccJit.getLeanIncRef.run state context
  let _ ← GccJit.getLeanAllocSmallObject.run state context
  let _ ← GccJit.getLeanAllocCtorMemory.run state context
  -- let _ ← GccJit.getLeanDecRef.run state context
  -- let _ ← GccJit.getLeanIncN.run state context
  ctx.setBoolOption BoolOption.DumpInitialGimple true
  ctx.compileToFile OutputKind.ObjectFile "/tmp/test.o"
  ctx.release
