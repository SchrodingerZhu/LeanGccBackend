import LeanGccBackend.Basic
import LeanGccBackend.Runtime
import Lean.Compiler.IR.Boxing
import LeanGccJit.Core
import Lean.Compiler.IR.EmitC
open LeanGccJit.Core

namespace Lean.IR
open ExplicitBoxing
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
  func      : Func
  params    : HashMap String LeanGccJit.Core.Param
  cursor    : Block
  tmpCount  : Nat
  localVars : HashMap VarId LValue
  entry     : Block
  
abbrev FuncM := StateT FunctionView CodegenM 

def getParamM! (n : String) : FuncM LeanGccJit.Core.Param := do
  match (← get).params.find? n with
  | some p => pure p
  | _ => throw s!"unknown parameter {n}"

def withFunctionView 
  (func: Func) (entry: Block) (params: Array (LeanGccJit.Core.Param × String)) (body: FuncM α) : CodegenM α := do 
  let mut params' := HashMap.empty
  for (p, name) in params do
    params' := params'.insert name p
  body.run' ⟨func, params', entry, 0, default, entry⟩

def moveTo (blk: Block) : FuncM Unit := do
  modify fun view => { view with cursor := blk }

def currentBlock : FuncM Block := do
  get >>= (pure ·.cursor)

def getFunction : FuncM Func := 
  get >>= (pure ·.func)

def getNewLocalName : FuncM String := do
  let tmpCount ← get >>= (pure ·.tmpCount)
  modify fun view => { view with tmpCount := tmpCount + 1 }
  pure s!"_Tv{tmpCount}"

def mkIndexVarM (ty: JitType) (id : VarId) : FuncM LValue := do
  match (← get).localVars.find? id with
  | none => do
    let name := s!"_Iv{id}"
    let lval ← getFunction >>= (·.newLocal none ty name)
    modify fun view => { view with localVars := view.localVars.insert id lval }
    pure lval
  | some lval => pure lval

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
  (varArgs : Bool := false)
  : CodegenM Func := getOrCreateFunction name do
    let ctx ← getCtx
    let params' ← params.mapM fun (ty, name) => do ctx.newParam none ty name
    let func ← ctx.newFunction none kind retTy name params' varArgs
    match kind with
    | FunctionKind.Imported => 
      return func
    | _ => do
      let block ← func.newBlock "entry"
      let params'' := params'.zip $ params.map (·.2)
      withFunctionView func block params'' body
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
          mkAssignmentM res (←call i (← getParamM! "builtin", ← getParamM! "w"))
          let isErr ← call (← getLeanIOResultIsError) res
          mkIfBranchM isErr
            (do 
              mkReturnM res
            )
            (do 
              mkEvalM (←call (← getLeanDecRef) res)
            )
        currentBlock >>= (·.addComment none "TODO: generate decl init code")
        goto epilogue 
      )
    moveTo epilogue
    let unit ← call (← getLeanBox) (← constantZero (← size_t))
    let ok ← call (← getLeanIOResultMkOk) unit
    mkReturnM ok

def toCType : IRType → CodegenM JitType
  | IRType.float      => double
  | IRType.uint8      => uint8_t
  | IRType.uint16     => uint16_t
  | IRType.uint32     => uint32_t
  | IRType.uint64     => uint64_t
  | IRType.usize      => size_t
  | IRType.object     => «lean_object*»
  | IRType.tobject    => «lean_object*»
  | IRType.irrelevant => «lean_object*»
  | IRType.struct _ _ => throw "IRType.struct cannot be converted to JitType yet"
  | IRType.union _ _  => throw "IRType.union cannot be converted to JitType yet"

def throwInvalidExportName {α : Type} (n : Name) : CodegenM α :=
  throw s!"invalid export name '{n}'"

def toCName (n : Name) : CodegenM String := do
  let env ← getEnv;
  match getExportNameFor? env n with
  | some (.str .anonymous s) => pure s
  | some _                   => throwInvalidExportName n
  | none                     => if n == `main then pure leanMainFn else pure n.mangle

def emitFnDeclAux (decl : Decl) (cppBaseName : String) (isExternal : Bool) : CodegenM Unit := do
  let ps := decl.params
  let env ← getEnv
  let kind := if ps.isEmpty && isClosedTermName env decl.name then
    FunctionKind.Internal
  else
    if isExternal then FunctionKind.Imported
    else FunctionKind.Exported
  let retTy ← toCType decl.resultType
  let ps := if isExternC env decl.name then ps.filter (fun p => !p.ty.isIrrelevant) else ps
  let ctx ← getCtx
  let params ←
    if ps.size > closureMaxArgs && isBoxedName decl.name then do
      pure #[← ctx.newParam none (← «lean_object*» >>= (·.getPointer)) "args"]
    else do
      let names := ps.map (fun p => s!"arg{p.x.idx}")
      let tys ← ps.mapM fun p => toCType p.ty
      let mut params := #[]
      for (ty, name) in tys.zip names do
        let param ← ctx.newParam none ty name
        params := params.push param
      pure params
  let func ← ctx.newFunction none kind retTy cppBaseName params false
  modify fun s => { s with declMap := s.declMap.insert decl.name func }

def emitExternDeclAux (decl : Decl) (cName : String) : CodegenM Unit := do
  let env ← getEnv
  let extC := isExternC env decl.name
  emitFnDeclAux decl cName extC

def emitFnDecl (decl : Decl) (isExternal : Bool) : CodegenM Unit := do
  let cppBaseName ← toCName decl.name
  emitFnDeclAux decl cppBaseName isExternal

def emitFnDecls : CodegenM Unit := do
  let env ← getEnv
  let decls := getDecls env
  let modDecls  : NameSet := decls.foldl (fun s d => s.insert d.name) {}
  let usedDecls : NameSet := decls.foldl (fun s d => collectUsedDecls env d (s.insert d.name)) {}
  let usedDecls := usedDecls.toList
  usedDecls.forM fun n => do
    let decl ← getDecl n;
    match getExternNameFor env `c decl.name with
    | some cName => emitExternDeclAux decl cName
    | none       => emitFnDecl decl (!modDecls.contains n)

def argsRValue (args : Array Arg) : FuncM (Array RValue) := 
  args.mapM fun arg => 
    match arg with
    | Arg.var x => do (mkIndexVarM (←«lean_object*») x) >>= (·.asRValue)
    | Arg.irrelevant => do call (← getLeanBox) (← constantZero (← size_t))
  
def emitApp (z: LValue) (f : VarId) (args : Array Arg) : FuncM Unit := do
  let f ← mkIndexVarM (←«lean_object*») f
  let args ← argsRValue args
  if args.size <= closureMaxArgs then do
    mkAssignmentM z $ ← callArray (← getLeanApply args.size) (#[←  asRValue f] ++ args)
  else do
    let args ← getTempArrayObjArray args
    mkAssignmentM z $ ← call (← getLeanApplyM) (f, args)

def getFuncDecl (n : FunId) : CodegenM Func := do
  let f ← get >>= (pure $ ·.declMap.find? n)
  match f with
  | some f => pure f
  | none   => throw s!"unknown function {n}"

def emitMarkPersistent [AsRValue τ] (d : Decl) (val : τ) : FuncM Unit := do
  if d.resultType.isObj then
    mkEvalM (←call (← getLeanMarkPersistent) val)

def getTag [AsRValue τ] (xType : IRType) (val : τ) : FuncM RValue := do
  if xType.isObj then do
    call (← getLeanObjTag) val
  else
    asRValue val

def emitLit (z : LValue) (t : IRType) (v : LitVal) : FuncM Unit := do
  mkAssignmentM z $ ← match v with
  | LitVal.num n => do
    mkConstant (← toCType t) n.toUInt64
  | LitVal.str s => do
    let char ← char
    let ctx ← getCtx
    let length := s.utf8ByteSize
    let arr ← ctx.newArrayType none char length
    let gv ← getAnnoymousGlobal arr >>= (Global.setInitializer · s.toUTF8)
    let cstr ← arrayToPtr gv
    let length ← mkConstant (←size_t) length.toUInt64
    call (← getLeanMkStringFromBytes) (cstr, length)

def emitIsShared (z : LValue) (x : VarId) : FuncM Unit := do
  let x ← mkIndexVarM (←«lean_object*») x
  mkAssignmentM z $ ← call (← getLeanIsShared) x

def dispatchUnbox (t : IRType) : CodegenM Func :=
  match t with
  | IRType.usize  => do getLeanUnboxAux "size_t" (← size_t) 
  | IRType.uint32 => do getLeanUnboxAux "uint32_t" (← uint32_t)
  | IRType.uint64 => do getLeanUnboxAux "uint64_t" (← uint64_t)
  | IRType.float  => do getLeanUnboxAux "float" (← double)
  | _             => getLeanUnbox

def emitUnbox (z : LValue) (t : IRType) (x : VarId) : FuncM Unit := do
  let x ← mkIndexVarM (←«lean_object*») x
  let unbox ← dispatchUnbox t
  mkAssignmentM z $ ← call unbox x

def dispatchBox (t : IRType) : CodegenM Func :=
  match t with
  | IRType.usize  => do getLeanBoxAux "size_t" (← size_t) 
  | IRType.uint32 => do getLeanBoxAux "uint32_t" (← uint32_t)
  | IRType.uint64 => do getLeanBoxAux "uint64_t" (← uint64_t)
  | IRType.float  => do getLeanBoxAux "float" (← double)
  | _             => getLeanBox

def emitBox (z : LValue) (x : VarId) (t : IRType) : FuncM Unit := do
  let x ← mkIndexVarM (←«lean_object*») x
  let box ← dispatchBox t
  mkAssignmentM z $ ← call box x

def emitPartialApp (z : LValue) (f : FunId) (args : Array Arg) : FuncM Unit := do
  let decl ← getDecl f
  let f ← getFuncDecl f
  let address ← f.getAddress none
  let arity ← mkConstant  (←unsigned) decl.params.size.toUInt64;
  let fixed ← mkConstant  (←unsigned) args.size.toUInt64;
  mkAssignmentM z $ ← call (← getLeanAllocClosure) (address, arity, fixed)
  let mut idx := 0
  for arg in (← argsRValue args) do
    let idx' ← mkConstant (←unsigned) idx.toUInt64
    mkEvalM $ ←call (← getLeanClosureSet) (z, idx', arg)
  
def emitVDecl (z : VarId) (t : IRType) (v : Expr) : FuncM Unit := do
  let z ← mkIndexVarM (← toCType t) z
  match v with
  -- | Expr.ctor c ys      => emitCtor z c ys
  -- | Expr.reset n x      => emitReset z n x
  -- | Expr.reuse x c u ys => emitReuse z x c u ys
  -- | Expr.proj i x       => emitProj z i x
  -- | Expr.uproj i x      => emitUProj z i x
  -- | Expr.sproj n o x    => emitSProj z t n o x
  -- | Expr.fap c ys       => emitFullApp z c ys
    | Expr.pap c ys       => emitPartialApp z c ys
    | Expr.ap x ys        => emitApp z x ys
    | Expr.box t x        => emitBox z x t
    | Expr.unbox x        => emitUnbox z t x
    | Expr.isShared x     => emitIsShared z x
    | Expr.lit v          => emitLit z t v
    | _                   => throw "not implemented"


def emitMainFn : CodegenM Unit := do
  let env ← getEnv
  -- let main ← getDecl `main
  -- let params ← match main with
  --  | .fdecl (xs := xs) .. => pure xs
  --  | _ =>  throw "Function declaration expected for 'main'"
  let int ← int
  let bool ← bool
  let argv ← «const char*» >>= (·.getPointer)
  discard $ mkFunctionM "main" int #[(int, "argc"), (argv, "argv")] (kind := FunctionKind.Exported) do
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
          let argc ← getParamM! "argc"
          let argv ← getParamM! "argv"
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