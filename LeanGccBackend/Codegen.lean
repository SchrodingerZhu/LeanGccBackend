import LeanGccBackend.Basic
import LeanGccBackend.Runtime
import LeanGccJit.Core
open LeanGccJit.Core

namespace Lean.IR
namespace GccJit

def getEnv : CodegenM Environment := read >>= (pure ·.env)
def getModName : CodegenM Name := GccContext.modName <$> read

def getDecl (n : Name) : CodegenM Decl := do
  let env ← getEnv
  match findEnvDecl env n with
  | some d => pure d
  | none   => throw s!"unknown declaration {n}"

def Constant.SEM_FAILCRITICALERRORS : CodegenM RValue := do
  mkConstant (←unsigned) 1 

def getSetErrorMode : CodegenM Func := do
  importFunction "SetErrorMode" (←unsigned) #[((←unsigned), "uMode")]

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

structure FunctionView where
  func : Func
  params: Array LeanGccJit.Core.Param
  cursor : Block
  tmpCount : Nat

abbrev FuncM := StateT FunctionView CodegenM 

def getParamM! (n : Nat) : FuncM LeanGccJit.Core.Param := do
  get >>= (getParam! ·.params n)

def withFunctionView 
  (func: Func) (entry: Block) (params: Array LeanGccJit.Core.Param) (body: FuncM α) : CodegenM α := do 
  body.run' ⟨func, params, entry, 0⟩

def moveTo (blk: Block) : FuncM Unit := do
  modify fun view => { view with cursor := blk }

def currentBlock : FuncM Block := do
  get >>= (pure ·.cursor)

def getFunction : FuncM Func := 
  get >>= (pure ·.func)

def getNewLocalName : FuncM String := do
  let tmpCount ← get >>= (pure ·.tmpCount)
  modify fun view => { view with tmpCount := tmpCount + 1 }
  pure s!"__tmp{tmpCount}"

def mkLocalVarM (ty: JitType) (name : Option String := none) : FuncM LValue := do
  match name with
  | none => do 
    let name ← getNewLocalName
    getFunction >>= (·.newLocal none ty name)
  | some name => do
    getFunction >>= (·.newLocal none ty name)

def mkAssignmentM [AsLValue α] [AsRValue τ] (x : α) (y : τ) : FuncM Unit := do
  mkAssignment (←currentBlock) x y

def mkAssignmentOpM [AsLValue α] [AsRValue τ]  (op : BinaryOp) (x : α) (y : τ) : FuncM Unit := do
  mkAssignmentOp (←currentBlock) op (← asLValue x) (← asRValue y)

def mkEvalM [AsRValue τ] (x : τ) : FuncM Unit := do
  mkEval (←currentBlock) x

def getTempArrayObjArray (objs : Array RValue) : FuncM LValue := do
  let obj_ptr ← «lean_object*»
  let ctx ← getCtx
  let arrTy ← ctx.newArrayType none obj_ptr objs.size
  let arr ← mkLocalVarM arrTy
  let constructor ← ctx.newArrayConstructor none arrTy objs
  mkAssignmentM arr constructor
  return arr

def mkFunctionM
  (name : String) 
  (retTy : JitType) 
  (params : Array (JitType × String)) 
  (body: FuncM Unit)
  (kind : FunctionKind := FunctionKind.AlwaysInline)
  : CodegenM Func := getOrCreateFunction name do
    let ctx ← getCtx
    let params' ← params.mapM fun (ty, name) => do ctx.newParam none ty name
    let func ← ctx.newFunction none kind retTy name params' false
    match kind with
    | FunctionKind.Imported => 
      return func
    | _ => do
      let block ← func.newBlock "entry"
      withFunctionView func block params' body
      pure func

def mkNewBlock (name : Option String := none) : FuncM Block := do
  getFunction >>= (·.newBlock name)

def mkIfBranchM [AsRValue τ] (cond: τ)
  (then_ : FuncM Unit)
  (else_ : FuncM Unit) 
  (thenName : Option String := none)
  (elseName : Option String := none)
: FuncM Unit := do
  let onTrue ← mkNewBlock thenName
  let onFalse ← mkNewBlock elseName
  let blk ← currentBlock
  blk.endWithConditional none (← asRValue cond) onTrue onFalse
  moveTo onTrue
  then_
  moveTo onFalse
  else_

def goto (x : Block) : FuncM Unit :=
  currentBlock >>= (·.endWithJump none x)

def mkReturnM [AsRValue τ] (x : τ) : FuncM Unit := do
  mkReturn (←currentBlock) x

def getModuleInitializationFunction : CodegenM Func := do
  let bool ← bool
  let uint8_t ← uint8_t
  let obj_ptr ← «lean_object*»
  let env ← getEnv
  let modName ← getModName
  let mut importedInits := #[]
  for i in env.imports do
    let f ← importFunction (mkModuleInitializationFunctionName i.module) obj_ptr #[(uint8_t, "builtin"), (obj_ptr, "w")]
    importedInits := importedInits.push f
  let _G_initialized ← getOrCreateGlobal "_G_initialized" bool (init := ←constantZero bool)
  mkFunctionM (mkModuleInitializationFunctionName modName) obj_ptr #[(uint8_t, "builtin"), (obj_ptr, "w")] (kind := FunctionKind.Exported) do
    let res ← mkLocalVarM obj_ptr "res"
    let epilogue ← mkNewBlock "epilogue"
    mkIfBranchM _G_initialized 
      (do
        goto epilogue
      )
      (do 
        mkAssignmentM _G_initialized (← constantOne bool)
        for i in importedInits do
          mkAssignmentM res (←call i (← getParamM! 0, ← getParamM! 1))
          let isErr ← call (← getLeanIOResultIsError) res
          mkIfBranchM isErr
            (do 
              mkReturnM res
            )
            (do 
              mkEvalM (←call (← getLeanDecRef) res)
            )
        goto epilogue 
      )
    moveTo epilogue
    epilogue.addComment none "TODO: generate decl init code"
    let unit ← call (← getLeanBox) (← constantZero (← size_t))
    let ok ← call (← getLeanIOResultMkOk) unit
    mkReturnM ok


def emitMainFn : CodegenM Unit := do
  let env ← getEnv
  -- let main ← getDecl `main
  -- let params ← match main with
  --  | .fdecl (xs := xs) .. => pure xs
  --  | _ =>  throw "Function declaration expected for 'main'"
  let int ← int
  let bool ← bool
  let argv ← «const char*» >>= (·.getPointer)
  let _ ← mkFunctionM "main" int #[(int, "argc"), (argv, "argv")] (kind := FunctionKind.Exported) do
    if System.Platform.getIsWindows () then do
      mkEvalM (←call (←getSetErrorMode) (←Constant.SEM_FAILCRITICALERRORS))
    let usesLeanAPI := usesModuleFrom env `Lean
    if usesLeanAPI then do
      mkEvalM (←call (← getLeanInitialize) ())
    else do
      mkEvalM (←call (← getLeanInitializeRuntimeModule) ())
    mkEvalM (←call (← getLeanSetPanicMessages) (← constantZero bool))
    let res ← mkLocalVarM (←«lean_object*») "res"
    let realWorld ← call (← getLeanIOMkWorld) ()
    mkAssignmentM res (←call (← getModuleInitializationFunction) ((← constantOne (← uint8_t)), realWorld))
    mkEvalM (←call (← getLeanSetPanicMessages) (← constantOne bool))
    mkEvalM (←call (← getLeanIOMarkEndInitialization) ())
    let leanMain ← getLeanMain
    let epilogue ← mkNewBlock "epilogue"
    mkIfBranchM (← call (← getLeanIOResultIsOk) res)
      (do 
        mkEvalM (←call (← getLeanDecRef) res)
        mkEvalM (←call (← getLeanInitTaskManager) ())
        if (←leanMain.getParamCount) == 2
        then
          let argc ← getParamM! 0
          let argv ← getParamM! 1
          let argList ← call (← getCStrArrayToLeanList) (argc, argv)
          mkAssignmentM res (←call (← getLeanMain) (argList, realWorld))
        else
          mkAssignmentM res (←call (← getLeanMain) (realWorld))
        goto epilogue
      )
      (goto epilogue)
    let retTy := 
      env.find? `main |>.map (·.type |>.getForallBody |>.appArg!) |>.getD default
    moveTo epilogue
    mkEvalM (←call (← getLeanFinalizeTaskManager) ())
    mkIfBranchM (← call (← getLeanIOResultIsOk) res)
      (do 
        let ret ← mkLocalVarM int "ret"
        if retTy.constName? == some ``UInt32 then do
          let inner ← call (← getLeanIOResultGetValue) res
          let unboxed ← (← call (← getLeanUnboxUInt32) inner) ::! (← int32_t)
          let extended ← unboxed ::: int
          mkAssignmentM ret extended
        else do
          mkAssignmentM ret (← constantZero int)
        mkEvalM (←call (← getLeanDecRef) res)
        mkReturnM ret
      )
      (do 
        mkEvalM (←call (← getLeanIOResultShowError) res)
        mkEvalM (←call (← getLeanDecRef) res)
        mkReturnM (← constantOne int)
      )
  return