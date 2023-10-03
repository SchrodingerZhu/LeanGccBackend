import LeanGccBackend.Basic
import LeanGccBackend.Runtime
import LeanGccJit.Core
open LeanGccJit.Core

namespace Lean.IR
namespace GccJit

def getEnv : CodegenM Environment := read >>= (pure ·.env)

def getDecl (n : Name) : CodegenM Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => throw s!"unknown declaration {n}"

def Constant.SEM_FAILCRITICALERRORS : CodegenM RValue := do
  mkConstant (←unsigned) 1 

def getSetErrorMode : CodegenM Func := do
  importFunction "SetErrorMode" (←unsigned) #[((←unsigned), "uMode")]

def getModuleInitializationFunction : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  importFunction "__TODO__MODULE_INITIALIZATION_FUNCTION" obj_ptr #[
    ((←int8_t), "x"), (obj_ptr, "y")
  ]

def getLeanMain : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  importFunction "__TODO__LEAN_MAIN" obj_ptr #[
    (obj_ptr, "arg_list"), (obj_ptr, "real_world")
  ]

def getCStrArrayToLeanList : CodegenM Func := do
  let cstr ← «const char*»
  let obj_ptr ← «lean_object*»
  let unsigned ← unsigned
  let int ← int
  mkFunction "__lean_internal_cstr_array_to_lean_list" obj_ptr (kind := FunctionKind.Internal) 
    #[(int, "argc"), (← cstr.getPointer, "argv")] fun blk params => do
    let n ← getParam! params 0
    let cstrArr ← getParam! params 1 
    let list ← mkLocalVar blk obj_ptr "list"
    mkAssignment blk list (←call (← getLeanBox) (← constantZero (← size_t)))
    mkWhileLoop blk (← n ·>> (← constantOne int))
      (fun body => do
        mkAssignmentOp body BinaryOp.Minus n (← constantOne int)
        let cstr ← mkArrayAccess cstrArr n
        let str ← call (← getLeanMkString) cstr
        let ctor ← mkLocalVar body obj_ptr "ctor"
        mkAssignment body ctor (←call (← getLeanAllocCtor) 
          (← constantOne unsigned, ← mkConstant unsigned 2, ← mkConstant unsigned 0))
        mkEval body $ (←call (← getLeanCtorSet) (ctor, ← constantZero unsigned, str))
        mkEval body $ (←call (← getLeanCtorSet) (ctor, ← constantOne unsigned, list))
        mkAssignment body list ctor
      )
      (fun after => mkReturn after list)

def emitMainFn : CodegenM Unit := do
  let env ← getEnv
  -- let main ← getDecl `main
  -- let params ← match main with
  --  | .fdecl (xs := xs) .. => pure xs
  --  | _ =>  throw "Function declaration expected for 'main'"
  let int ← int
  let bool ← bool
  let argv ← «const char*» >>= (·.getPointer)
  let body := fun blk params => do
    if System.Platform.getIsWindows () then do
      mkEval blk $ (←call (←getSetErrorMode) (←Constant.SEM_FAILCRITICALERRORS))
    let usesLeanAPI := usesModuleFrom env `Lean
    if usesLeanAPI then do
      mkEval blk $ (←call (← getLeanInitialize) ())
    else do
      mkEval blk $ (←call (← getLeanInitializeRuntimeModule) ())
    mkEval blk $ (←call (← getLeanSetPanicMessages) (← constantZero bool))
    let res ← mkLocalVar blk (←«lean_object*») "res"
    let realWorld ← call (← getLeanIOMkWorld) ()
    mkAssignment blk res (←call (← getModuleInitializationFunction) ((← constantOne (← int8_t)), realWorld))
    mkEval blk $ (←call (← getLeanSetPanicMessages) (← constantOne bool))
    mkEval blk $ (←call (← getLeanIOMarkEndInitialization) ())
    let leanMain ← getLeanMain
    let func ← blk.getFunction
    let epilogue ← func.newBlock "epilogue"
    mkIfBranch blk (← call (← getLeanIOResultIsOk) res)
      (fun then_ => do 
        mkEval then_ $ (←call (← getLeanDecRef) res)
        mkEval then_ $ (←call (← getLeanInitTaskManager) ())
        if (←leanMain.getParamCount) == 2
        then
          let argc ← getParam! params 0
          let argv ← getParam! params 1
          let argList ← call (← getCStrArrayToLeanList) (argc, argv)
          mkAssignment then_ res $ (←call (← getLeanMain) (argList, realWorld))
        else
          mkAssignment then_ res $ (←call (← getLeanMain) (realWorld))
        then_.endWithJump none epilogue
      )
      (fun else_ => do 
        else_.endWithJump none epilogue 
      )
    let retTy := 
      env.find? `main |>.map (·.type |>.getForallBody |>.appArg!) |>.getD default
    mkEval epilogue $ (←call (← getLeanFinalizeTaskManager) ())
    mkIfBranch epilogue (← call (← getLeanIOResultIsOk) res)
      (fun then_ => do 
        let ret ← mkLocalVar then_ int "ret"
        if retTy.constName? == some ``UInt32 then do
          let inner ← call (← getLeanIOResultGetValue) res
          let unboxed ← (← call (← getLeanUnboxUInt32) inner) ::! (← int32_t)
          let extended ← unboxed ::: int
          mkAssignment then_ ret extended
        else do
          mkAssignment then_ ret (← constantZero int)
        mkEval then_ $ (←call (← getLeanDecRef) res)
        mkReturn then_ ret
      )
      (fun else_ => do 
        mkEval else_ $ (←call (← getLeanIOResultShowError) res)
        mkEval else_ $ (←call (← getLeanDecRef) res)
        mkReturn else_ (← constantOne int)
      )
  let _ ← mkFunction "main" int #[(int, "argc"), (argv, "argv")] body FunctionKind.Exported
  return