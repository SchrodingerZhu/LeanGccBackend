import «LeanGccBackend»
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
    let _ ← GccJit.getLeanBox
    let _ ← GccJit.getLeanUnbox
    let _ ← GccJit.getLeanPtrTag
    let _ ← GccJit.getLeanPtrOther
    let _ ← GccJit.getLeanAllocSmallObject
    let _ ← GccJit.getLeanAllocCtorMemory
    let _ ← GccJit.getLeanIsMT
    let _ ← GccJit.getLeanIncRef
    let _ ← GccJit.getLeanIncRefN
    let _ ← GccJit.getLeanDecRef
    let _ ← GccJit.getLeanInc
    let _ ← GccJit.getLeanIncN
    let _ ← GccJit.getLeanDec
    let _ ← GccJit.getLeanObjTag
    let _ ← GccJit.getLeanIsExclusive
    let _ ← GccJit.getLeanIsShared
    let _ ← GccJit.getLeanCtorObjCPtr
    let _ ← GccJit.getLeanCtorSet
    let _ ← GccJit.getCStrArrayToLeanList
    let _ ← GccJit.getModuleInitializationFunction
    let _ ← GccJit.getLeanAllocClosure
    discard $ GccJit.getLeanClosureSet
    GccJit.emitMainFn
  
  let _ ← ops.run state context
  -- let _ ← GccJit.getLeanDecRef.run state context
  -- let _ ← GccJit.getLeanIncN.run state context
  ctx.setBoolOption BoolOption.DumpInitialGimple true
  ctx.compileToFile OutputKind.ObjectFile "/tmp/test.o"
  ctx.release
