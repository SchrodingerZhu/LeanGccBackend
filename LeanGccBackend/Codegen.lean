import LeanGccBackend.Basic
import LeanGccBackend.Runtime
import Lean.Compiler.IR.Boxing
import LeanGccJit.Core
import Lean.Compiler.IR.EmitC
import Lean.Compiler.IR.EmitLLVM
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

def getFuncDecl (n : FunId): CodegenM Func := do
  let f ← get >>= (pure $ ·.declMap.find? n)
  match f with
  | some f => pure f.fst
  | none   => throw s!"unknown function {n}"

def getFuncDecl' (n : FunId): CodegenM (Func × Array (LeanGccJit.Core.Param × String)) := do
  let f ← get >>= (pure $ ·.declMap.find? n)
  match f with
  | some f => pure f
  | none   => throw s!"unknown function {n}"  

def throwInvalidExportName {α : Type} (n : Name) : CodegenM α :=
  throw s!"invalid export name '{n}'"

def toCInitName (n : Name) : CodegenM String := do
  let env ← getEnv;
  -- TODO: we should support simple export names only
  match getExportNameFor? env n with
  | some (.str .anonymous s) => return "_init_" ++ s
  | some _                   => throwInvalidExportName n
  | none                     => pure ("_init_" ++ n.mangle)

def dispatchUnbox (t : IRType) : CodegenM Func :=
  match t with
  | IRType.usize  => do getLeanUnboxAux "size_t" (← size_t) 
  | IRType.uint32 => do getLeanUnboxAux "uint32_t" (← uint32_t)
  | IRType.uint64 => do getLeanUnboxAux "uint64_t" (← uint64_t)
  | IRType.float  => do getLeanUnboxAux "float" (← double)
  | _             => getLeanUnbox

def Constant.SEM_FAILCRITICALERRORS : CodegenM RValue := do
  mkConstant (←unsigned) 1 

def getSetErrorMode : CodegenM Func := do
  importFunction "SetErrorMode" (←unsigned) #[((←unsigned), "uMode")]

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
  jps       : HashMap JoinPointId (Block × Array LValue)
  decl      : Option Decl
  
abbrev FuncM := StateT FunctionView CodegenM 

def getParamM! (n : String) : FuncM LeanGccJit.Core.Param := do
  match (← get).params.find? n with
  | some p => pure p
  | _ => throw s!"unknown parameter {n}"

def withFunctionView 
  (func: Func) (entry: Block) (params: Array (LeanGccJit.Core.Param × String)) (body: FuncM α) (decl: Option Decl := none) : CodegenM α := do 
  let mut params' := HashMap.empty
  for (p, name) in params do
    params' := params'.insert name p
  body.run' ⟨func, params', entry, 0, default, entry, default, decl⟩

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

def declareIndexVar (ty : JitType) (id : VarId) : FuncM LValue := do
  match (← get).localVars.find? id with
  | none => do
    let func ← getFunction
    let lval ← func.newLocal none ty s!"{id}"
    modify fun view => { view with localVars := view.localVars.insert id lval }
    return lval
  | some lval => 
    return lval

def getIndexVar (id : VarId) : FuncM LValue := do
  match (← get).localVars.find? id with
  | none => throw s!"unknown local variable {id}"
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

def toCName (n : Name) : CodegenM String := do
  let env ← getEnv;
  match getExportNameFor? env n with
  | some (.str .anonymous s) => pure s
  | some _                   => throwInvalidExportName n
  | none                     => if n == `main then pure leanMainFn else pure n.mangle

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

def emitDeclInit (d : Decl) (res: LValue) (errBlk: Block) (w : RValue) : FuncM Unit := do
  let env ← getEnv
  let n := d.name
  let builtin ← getParamM! "builtin" >>= (·.asRValue)
  if isIOUnitInitFn env n then do
    let f ← getFuncDecl $ ← toCName n
    let mut nextBlk := none
    if isIOUnitBuiltinInitFn env n then do
      let blkBuiltin ← mkNewBlock
      let blkNotBuiltin ← mkNewBlock
      currentBlock >>= (·.endWithConditional none builtin blkBuiltin blkNotBuiltin)
      nextBlk := some blkNotBuiltin
      moveTo blkBuiltin
    mkAssignmentM res $ ← call f w
    let isErr ← call (← getLeanIOResultIsError) res
    let next ← match nextBlk with
    | some blk => pure blk
    | none => mkNewBlock
    currentBlock >>= (·.endWithConditional none isErr errBlk next)
    moveTo next
    mkEvalM $ ←call (← getLeanDecRef) res
  else if d.params.size == 0 then do
    let gv ← getOrCreateGlobal (← toCName n) (← toCType d.resultType)
    match getInitFnNameFor? env n with
    | some initFn =>
      let mut nextBlk := none
      if getBuiltinInitFnNameFor? env n |>.isSome then
        let blkBuiltin ← mkNewBlock
        let blkNotBuiltin ← mkNewBlock
        currentBlock >>= (·.endWithConditional none builtin blkBuiltin blkNotBuiltin)
        nextBlk := some blkNotBuiltin
        moveTo blkBuiltin
      let f ← getFuncDecl $ ← toCName initFn
      mkAssignmentM res $ ← call f w
      let isErr ← call (← getLeanIOResultIsError) res
      let next ← match nextBlk with
      | some blk => pure blk
      | none => mkNewBlock
      currentBlock >>= (·.endWithConditional none isErr errBlk next)
      moveTo next
      let value ← call (← getLeanIOResultGetValue) res
      if d.resultType.isScalar then
        let unboxed ← call (← dispatchUnbox d.resultType) value
        mkAssignmentM gv unboxed
      else
        mkAssignmentM gv value
        mkEvalM $ ←call (← getLeanMarkPersistent) gv
      mkEvalM $ ←call (← getLeanDecRef) res
    | _ =>
      let f ← getFuncDecl $ ← toCInitName n
      mkAssignmentM gv $ ← call f ()
      mkEvalM $ ←call (← getLeanMarkPersistent) gv

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
        let decls := getDecls env
        if !importedInits.isEmpty || !decls.isEmpty then do
          let errBlk ← mkNewBlock "err"
          errBlk.endWithReturn none $ ← res.asRValue
          let w ← getParamM! "w"
          for i in importedInits do
            mkAssignmentM res (←call i (← getParamM! "builtin", w))
            let isErr ← call (← getLeanIOResultIsError) res
            mkIfBranchM isErr
              (do 
                goto errBlk
              )
              (do 
                mkEvalM (←call (← getLeanDecRef) res)
              )
          decls.reverse.forM (emitDeclInit · res errBlk (← w.asRValue))
        goto epilogue 
      )
    moveTo epilogue
    let unit ← call (← getLeanBox) (← constantZero (← size_t))
    let ok ← call (← getLeanIOResultMkOk) unit
    mkReturnM ok

def emitFnDeclAux (decl : Decl) (cppBaseName : String) (isExternal : Bool) : CodegenM Unit := do
  let ps := decl.params
  let env ← getEnv
  let ctx ← getCtx
  if ps.isEmpty then do
    let kind := if isClosedTermName env decl.name then
      GlobalKind.Internal
    else if isExternal then 
      GlobalKind.Imported
    else GlobalKind.Exported
    let retTy ← toCType decl.resultType
    discard $ getOrCreateGlobal cppBaseName retTy (kind := kind)
    let name := "_init_" ++ cppBaseName
    let func ← ctx.newFunction none FunctionKind.Internal retTy name #[] false
    modify fun s => { s with declMap := s.declMap.insert name (func, #[]) }
  else do
    let kind := if isClosedTermName env decl.name then
      FunctionKind.Internal
    else if isExternal then 
      FunctionKind.Imported
    else FunctionKind.Exported
    let retTy ← toCType decl.resultType
    let ps := if isExternC env decl.name then ps.filter (fun p => !p.ty.isIrrelevant) else ps
    let (names, params) ←
      if ps.size > closureMaxArgs && isBoxedName decl.name then do
        pure (#["args"], #[← ctx.newParam none (← «lean_object*» >>= (·.getPointer)) "args"])
      else do
        let names := ps.map (fun p => s!"{p.x}")
        let tys ← ps.mapM fun p => toCType p.ty
        let mut params := #[]
        for (ty, name) in tys.zip names do
          let param ← ctx.newParam none ty name
          params := params.push param
        pure (names, params)
    let namedParams := params.zip names
    let func ← ctx.newFunction none kind retTy cppBaseName params false
    modify fun s => { s with declMap := s.declMap.insert cppBaseName (func, namedParams) }

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

def argRValue (arg : Arg) : FuncM RValue := 
  match arg with
    | Arg.var x => do getIndexVar x >>= (·.asRValue)
    | Arg.irrelevant => do call (← getLeanBox) (← constantZero (← size_t))

def argsRValue (args : Array Arg) : FuncM (Array RValue) := 
  args.mapM argRValue
  
def emitAppRV (f : VarId) (args : Array Arg) : FuncM RValue := do
  let f ← getIndexVar f
  let args ← argsRValue args
  if args.size <= closureMaxArgs then do
    callArray (← getLeanApply args.size) (#[←  asRValue f] ++ args)
  else do
    let args ← getTempArrayObjArray args
    call (← getLeanApplyM) (f, args)

def emitApp (z: LValue) (f : VarId) (args : Array Arg) : FuncM Unit := do
  mkAssignmentM z $ ← emitAppRV f args

def emitMarkPersistent [AsRValue τ] (d : Decl) (val : τ) : FuncM Unit := do
  if d.resultType.isObj then
    mkEvalM (←call (← getLeanMarkPersistent) val)

def getTag [AsRValue τ] (xType : IRType) (val : τ) : FuncM RValue := do
  if xType.isObj then do
    call (← getLeanObjTag) val
  else
    asRValue val

def emitCStringLit (s : String) : FuncM RValue := do
  let char ← char
  let ctx ← getCtx
  let length := s.utf8ByteSize
  let arr ← ctx.newArrayType none char length
  let (gv, initialized) ← getGlobalForLiteral s arr 
  if !initialized then do
    discard $ Global.setInitializer gv s.toUTF8
  (← arrayToPtr gv) ::: (←«const char*»)

def emitNumLit (t : IRType) (n : Nat) : FuncM RValue := do
  let limit : Nat := (((1 <<< (System.Platform.numBits - 2)) - 1) <<< 1) + 1
  if t.isObj then
    if n <= limit then
      call (← getLeanBox) $ ← mkConstant (← size_t) n.toUInt64
    else
      let cstr ← emitCStringLit $ toString n
      call (← getLeanCStrToNat) cstr
  else
    mkConstant (← toCType t) n.toUInt64

def emitLit (z : LValue) (t : IRType) (v : LitVal) : FuncM Unit := do
  mkAssignmentM z $ ← match v with
  | LitVal.num n => emitNumLit t n
  | LitVal.str s => do
    let length := s.utf8ByteSize
    let cstr ← emitCStringLit s
    let length ← mkConstant (←size_t) length.toUInt64
    call (← getLeanMkStringFromBytes) (cstr, length)
    
    

def emitIsShared (z : LValue) (x : VarId) : FuncM Unit := do
  let x ← getIndexVar x
  mkAssignmentM z $ ← call (← getLeanIsShared) x

def emitUnbox (z : LValue) (t : IRType) (x : VarId) : FuncM Unit := do
  let x ← getIndexVar x
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
  let x ← getIndexVar x
  let box ← dispatchBox t
  mkAssignmentM z $ ← call box x

def emitPartialApp (z : LValue) (f : FunId) (args : Array Arg) : FuncM Unit := do
  let decl ← getDecl f
  let f ← getFuncDecl (← toCName f)
  let address ← f.getAddress none
  let arity ← mkConstant  (←unsigned) decl.params.size.toUInt64;
  let fixed ← mkConstant  (←unsigned) args.size.toUInt64;
  mkAssignmentM z $ ← call (← getLeanAllocClosure) (address, arity, fixed)
  let mut idx := 0
  for arg in (← argsRValue args) do
    let idx' ← mkConstant (←unsigned) idx.toUInt64
    mkEvalM $ ←call (← getLeanClosureSet) (z, idx', arg)

def emitSimpleExternalCall (f : String) (ps : Array Param) (ys : Array Arg) (retTy : JitType) : FuncM RValue := do
  let mut ps' := #[]
  let mut ys' := #[]
  for (p, y) in ps.zip ys do
    if p.ty.isIrrelevant then
      continue
    ps' := ps'.push p
    ys' := ys'.push y
  let params ← ps'.mapM fun p => do
    let ty ← toCType p.ty
    pure (ty, s!"arg{p.x.idx}")
  let f ← importFunction f retTy params
  let args ← argsRValue ys'
  callArray f args

def emitExternCall (f : FunId) (ps : Array Param) (extData : ExternAttrData) (ys : Array Arg) (t : IRType) : FuncM RValue := do
  let t ← toCType t
  match getExternEntryFor extData `c with
  | some (ExternEntry.standard _ extFn) => emitSimpleExternalCall extFn ps ys t
  | some (ExternEntry.inline _ pat)     => throw s!"inline {pat} extern call is not implemented"
  | some (ExternEntry.foreign _ extFn)  => emitSimpleExternalCall extFn ps ys t
  | _ => throw s!"failed to emit extern application '{f}'"

def emitFullAppRV (f : FunId) (ys : Array Arg) (t : IRType) : FuncM RValue := do
  let decl ← getDecl f
  if ys.size == 0 then do
    let gv ← getOrCreateGlobal (← toCName f) (← toCType decl.resultType)
    gv.asRValue
  else do
    match decl with
    | Decl.extern _ ps _ extData => 
      emitExternCall f ps extData ys t
    | _ =>
      let func ← getFuncDecl (← toCName f)
      let args ← argsRValue ys
      callArray func args

def emitFullApp (z : LValue) (f : FunId) (ys : Array Arg) (t : IRType) : FuncM Unit := do
  mkAssignmentM z $ ← emitFullAppRV f ys t

def emitOffset (n : Nat) (offset : Nat) : FuncM RValue := do
  let unsigned ← unsigned
  let offset ← mkConstant unsigned offset.toUInt64
  if n > 0 then
    let ptrSz ← size_t >>= (·.getSize)
    let shift ← mkConstant unsigned (ptrSz * n).toUInt64
    return ← offset + shift
  else
    return offset

def emitSProj (z : LValue) (t : IRType) (n offset : Nat) (x : VarId) : FuncM Unit := do
  let f ← match t with
    | IRType.float  => getLeanCtorGetAux "float" (← double)
    | IRType.uint8  => getLeanCtorGetAux "uint8_t" (← uint8_t)
    | IRType.uint16 => getLeanCtorGetAux "uint16_t" (← uint16_t)
    | IRType.uint32 => getLeanCtorGetAux "uint32_t" (← uint32_t)
    | IRType.uint64 => getLeanCtorGetAux "uint64_t" (← uint64_t)
    | _             => throw "invalid instruction"
  let x ← getIndexVar x
  let offset ← emitOffset n offset
  mkAssignmentM z $ ← call f (x, offset)

def emitUProj (z : LValue) (n : Nat) (x : VarId) : FuncM Unit := do
  let x ← getIndexVar x
  let i ← mkConstant (←unsigned) n.toUInt64
  mkAssignmentM z $ ← call (← getLeanCtorGetUsize) (x, i)

def emitProj (z : LValue) (n : Nat) (x : VarId) : FuncM Unit := do
  let x ← getIndexVar x
  let i ← mkConstant (←unsigned) n.toUInt64
  mkAssignmentM z $ ← call (← getLeanCtorGet) (x, i)

def emitAllocCtor (z : LValue) (c : CtorInfo) : FuncM Unit := do
  let unsigned ← unsigned
  let scalarSz ← mkConstant unsigned $ (← size_t >>= (·.getSize)) * c.usize + c.ssize |>.toUInt64
  let numObjs ← mkConstant unsigned c.size.toUInt64
  let tag ← mkConstant unsigned c.cidx.toUInt64
  mkAssignmentM z $ ← call (← getLeanAllocCtor) (tag, numObjs, scalarSz)
  
def emitCtorSetArgs (z : LValue) (ys : Array Arg) : FuncM Unit := do
  let mut i := 0
  for y in ← argsRValue ys do
    mkEvalM $ ← call (← getLeanCtorSet) (z, ← mkConstant (←unsigned) i.toUInt64, y)
    i := i + 1

def emitReuse (z : LValue) (x : VarId) (c : CtorInfo) (updtHeader : Bool) (ys : Array Arg) : FuncM Unit := do
  let join ← mkNewBlock
  let x ← getIndexVar x
  let isScalar ← call (← getLeanIsScalar) x
  mkIfBranchM isScalar
    (do 
        emitAllocCtor z c
        goto join
    )
    (do
        mkAssignmentM z x
        if updtHeader then do
          let tag ← mkConstant (←unsigned) c.cidx.toUInt64
          mkEvalM $ ←call (← getLeanCtorSetTag) (z, tag)
        goto join
    )
  moveTo join
  emitCtorSetArgs z ys

def emitReset (z : LValue) (n : Nat) (x : VarId) : FuncM Unit := do
  let x ← getIndexVar x
  let join ← mkNewBlock
  let isExclusive ← call (← getLeanIsExclusive) x
  let unsigned ← unsigned
  mkIfBranchM isExclusive
    (do 
      n.forM fun i => do
        mkEvalM $ ←call (← getLeanCtorRelease) (x, ← mkConstant unsigned i.toUInt64)
      mkAssignmentM z x
      goto join
    )
    (do 
      mkEvalM $ ←call (← getLeanDecRef) x
      let unit ← call (← getLeanBox) (← constantZero (← size_t))
      mkAssignmentM z unit
      goto join
    )
  moveTo join

def emitCtor (z : LValue) (c : CtorInfo) (ys : Array Arg) : FuncM Unit := do
  if c.size == 0 && c.usize == 0 && c.ssize == 0 then do
    let unit ← call (← getLeanBox) (← constantZero (← size_t))
    mkAssignmentM z unit
  else do
    emitAllocCtor z c
    emitCtorSetArgs z ys

def emitVDecl (z : VarId) (t : IRType) (v : Expr) : FuncM Unit := do
  let z ← getIndexVar z
  match v with
    | Expr.ctor c ys      => emitCtor z c ys
    | Expr.reset n x      => emitReset z n x
    | Expr.reuse x c u ys => emitReuse z x c u ys
    | Expr.proj i x       => emitProj z i x
    | Expr.uproj i x      => emitUProj z i x
    | Expr.sproj n o x    => emitSProj z t n o x
    | Expr.fap c ys       => emitFullApp z c ys t
    | Expr.pap c ys       => emitPartialApp z c ys
    | Expr.ap x ys        => emitApp z x ys
    | Expr.box t x        => emitBox z x t
    | Expr.unbox x        => emitUnbox z t x
    | Expr.isShared x     => emitIsShared z x
    | Expr.lit v          => emitLit z t v

def tailCallCompatible (f : Func) (g : Func) : FuncM Bool := do
  let rf ← f.getReturnType >>= (·.unqualified)
  let rg ← g.getReturnType >>= (·.unqualified)
  if (← rf.isCompatibleWith rg) then do
    let fc ← f.getParamCount
    let gc ← g.getParamCount
    if fc == gc then do
      fc.allM fun i => do
        let fa ← f.getParam i >>= (·.asRValue) >>= (·.getType) >>= (·.unqualified)
        let ga ← g.getParam i >>= (·.asRValue) >>= (·.getType) >>= (·.unqualified)
        fa.isCompatibleWith ga
    else
      return false
  else
    return false

def isTailCall (x : VarId) (v : Expr) (b : FnBody) : FuncM Bool := do
  let state ← get
  match state.decl, v, b with
  | some d, Expr.fap f _, FnBody.ret (Arg.var y) => 
    if d.name == f && x == y then do
      let current ← getFunction
      let f ← getFuncDecl $ ← toCName f
      tailCallCompatible current f
    else 
      return false
  | _, _, _ => pure false

def emitTailCall (t: IRType) (v : Expr) : FuncM Unit := do
  let rv ← match v with
  | Expr.fap f ys => emitFullAppRV f ys t
  | Expr.ap f ys  => emitAppRV f ys
  | _ => throw "invalid tail call"
  rv.setBoolRequireTailCall true
  mkReturnM rv

def fakeDefaultReturn : FuncM RValue := do
  let f ← getFunction
  let retTy ← f.getReturnType
  if ← retTy.isIntegral then do
    mkConstant retTy 0
  else if ← retTy.isCompatibleWith (← double) then do
    let ctx ← getCtx
    ctx.newRValueFromDouble (← double) 0.0
  else if ← retTy.isPointer >>= (pure ·.isSome) then do
    let ctx ← getCtx
    ctx.null retTy
  else
    throw "invalid return type"

def emitUnreachable : FuncM Unit := do
  let panicFn ← getLeanInternalPanicUnreachable
  mkEvalM $ ←call panicFn ()
  let builtinUnreachable ← getBuiltinFunc "__builtin_unreachable"
  mkEvalM $ ←call builtinUnreachable ()
  mkReturnM $ ← fakeDefaultReturn

def emitInc (x : VarId) (n : Nat) (check : Bool) : FuncM Unit := do
  unless n > 0 do
    let x ← getIndexVar x
    if check then do 
      if n == 1 then do
        mkEvalM $ ←call (← getLeanInc) x
      else do
        let n ← mkConstant (←unsigned) n.toUInt64
        mkEvalM $ ←call (← getLeanIncN) (x, n)
    else do
      if n == 1 then do
        mkEvalM $ ←call (← getLeanIncRef) x
      else do
        let n ← mkConstant (←unsigned) n.toUInt64
        mkEvalM $ ←call (← getLeanIncRefN) (x, n)

def emitDec (x : VarId) (check : Bool) : FuncM Unit := do
  let x ← getIndexVar x
  if check then do 
    mkEvalM $ ←call (← getLeanDec) x
  else do
    mkEvalM $ ←call (← getLeanDecRef) x

def emitDel (x : VarId) : FuncM Unit := do
  let x ← getIndexVar x
  mkEvalM $ ←call (← getLeanFreeObject) x

def emitSetTag (x : VarId) (i : Nat) : FuncM Unit := do
  let x ← getIndexVar x
  let i ← mkConstant (←unsigned) i.toUInt64
  mkEvalM $ ←call (← getLeanCtorSetTag) (x, i)

def emitSet (x : VarId) (i : Nat) (y : Arg) : FuncM Unit := do
  let x ← getIndexVar x
  let y ← argRValue y
  let i ← mkConstant (←unsigned) i.toUInt64
  mkEvalM $ ←call (← getLeanCtorSet) (x, i, y)

def emitUSet (x : VarId) (i : Nat) (y : VarId) : FuncM Unit := do
  let x ← getIndexVar x
  let y ← getIndexVar y
  let i ← mkConstant (←unsigned) i.toUInt64
  mkEvalM $ ←call (← getLeanCtorSetUsize) (x, i, y)

def emitSSet (x : VarId) (i : Nat) (o : Nat) (y : VarId) (t : IRType) : FuncM Unit := do
  let f ← match t with
    | IRType.float  => do 
      getLeanCtorSetAux "float" $ ←double
    | IRType.uint8  => do
      getLeanCtorSetAux "uint8_t" $ ←uint8_t
    | IRType.uint16 => do
      getLeanCtorSetAux "uint16_t" $ ←uint16_t
    | IRType.uint32 => do
      getLeanCtorSetAux "uint32_t" $ ←uint32_t
    | IRType.uint64 => do
      getLeanCtorSetAux "uint64_t" $ ←uint64_t
    | _             => throw s!"invalid type for sset: {t}"
  let x ← getIndexVar x
  let y ← getIndexVar y
  let offset ← emitOffset o i
  mkEvalM $ ←call f (x, offset, y)

def getJoinPoint (j : JoinPointId) : FuncM (Block × Array LValue) := do
  let view ← get
  match view.jps.find? j with
  | some jp => pure jp
  | none    => throw s!"unknown join point {j}"

def emitJmp (j : JoinPointId) (ys : Array Arg) : FuncM Unit := do
  let (blk, params) ← getJoinPoint j
  if params.size != ys.size then
    throw s!"invalid number of arguments for join point {j}"
  else
    for (x, y) in params.zip $ ← argsRValue ys do
      mkAssignmentM x y
    goto blk

partial def declareVars (f : FnBody) : FuncM Unit := do
  match f with
  | FnBody.vdecl x t _ b => do
      let t ← toCType t
      discard $ declareIndexVar t x
      declareVars b
  | FnBody.jdecl _ xs _ b => do
      for param in xs do 
        let t ← toCType param.ty
        discard $ declareIndexVar t param.x
      declareVars b
  | e => do
      if e.isTerminal then pure () else declareVars e.body

mutual
partial def emitFnBody (b : FnBody) : FuncM Unit := do
  declareVars b
  emitBlock b

partial def emitJoinPoint (j : JoinPointId) (v : FnBody) : FuncM Unit := do
  let cursor ← currentBlock
  let jp ← getJoinPoint j
  moveTo jp.fst
  declareVars v
  emitBlock v
  moveTo cursor

partial def emitCase (typeId : Name) (x : VarId) (ty: IRType) (alts: Array Alt) : FuncM Unit := do
  currentBlock >>= (·.addComment none s!"case of {typeId}")
  let cursor ← currentBlock
  let x ← getIndexVar x
  let tag ← getTag ty x
  let mut cases := #[]
  let mut fallback := none
  let ctx ← getCtx
  for i in alts do
    match i with
    | Alt.ctor ctor body => do
      let blk ← mkNewBlock
      moveTo blk
      emitFnBody body
      let value ← mkConstant (←unsigned) ctor.cidx.toUInt64
      let case ← ctx.newCase value value blk
      cases := cases.push case
    | Alt.default body => do
      let blk ← mkNewBlock
      moveTo blk
      emitFnBody body
      fallback := some blk
  let default ← match fallback with
    | some blk => pure blk
    | none     => do
      let blk ← mkNewBlock
      moveTo blk
      emitUnreachable
      pure blk
  cursor.endWithSwitch none tag default cases
  
partial def emitBlock (b : FnBody) : FuncM Unit := 
  match b with
  | FnBody.jdecl j _ v b => do
    emitJoinPoint j v
    emitBlock b
  | FnBody.vdecl x t v b => do
    if ← isTailCall x v b then
      emitTailCall t v
    else
      emitVDecl x t v
      emitBlock b
  | FnBody.inc x n c p b => do
    unless p do emitInc x n c
    emitBlock b
  | FnBody.dec x n c p b => do
    if n != 1 then 
      throw "n != 1 when emitting dec"
    else
      unless p do emitDec x c
      emitBlock b
  | FnBody.del x b => do
     emitDel x
     emitBlock b
  | FnBody.setTag x i b => do
    emitSetTag x i
    emitBlock b
  | FnBody.set x i y b => do 
    emitSet x i y
    emitBlock b
  | FnBody.uset x i y b => do
    emitUSet x i y
    emitBlock b
  | FnBody.sset x i o y t b => do 
    emitSSet x i o y t
    emitBlock b
  | FnBody.mdata _ b           => emitBlock b
  | FnBody.ret x               => do
    mkReturnM $ ← argRValue x
  | FnBody.case u x xType alts => do
    emitCase u x xType alts
  | FnBody.jmp j xs            => emitJmp j xs
  | FnBody.unreachable         => emitUnreachable
end

def getLeanMain : CodegenM Func := do
  match ← getDecl `main with
  | Decl.fdecl f .. => getFuncDecl (← toCName f)
  | _ => throw "Function declaration expected for 'main'"

def emitMainFn : CodegenM Unit := do
  let env ← getEnv
  let main ← getDecl `main
  discard $ match main with
   | .fdecl (xs := xs) .. =>
      if xs.size != 1 && xs.size != 2 then
        throw "invalid main function"
      else do
        pure ()
   | _ => 
      throw "Function declaration expected for 'main'"
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
      (
        goto epilogue
      )
    moveTo epilogue
    mkEvalM (←call (← getLeanFinalizeTaskManager) ())
    let retTy := 
      env.find? `main |>.map (·.type |>.getForallBody |>.appArg!) |>.getD default
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

def hasMainFn : CodegenM Bool := do
  let env ← getEnv
  let decls := getDecls env
  return decls.any (fun d => d.name == `main)

def emitMainFnIfNeeded : CodegenM Unit := do
  if (← hasMainFn) then emitMainFn

def emitDeclAux (d : Decl) : CodegenM Unit := do
  let name ← if d.params.size > 0 then
    toCName d.name
  else
    toCInitName d.name
  let (func, params) ← getFuncDecl' name
  let (_, jpMap) := mkVarJPMaps d
  let entry ← func.newBlock "entry"
  withFunctionView func entry params (decl := some d) do
    match d with
    | .fdecl (xs := xs) (body := b) .. =>
      let jpMap : HashMap JoinPointId (Block × Array LValue) ← jpMap.foldM (init := HashMap.empty) fun m k v => do
        let name := s!"join_point_{k}"
        let blk ← mkNewBlock name
        let vars ← v.foldlM (init := #[]) fun m v => do
          let t ← toCType v.ty
          let x ← declareIndexVar t v.x
          pure $ m.push x
        pure $ m.insert k (blk, vars)
      modify fun s => { s with jps := jpMap }
      if xs.size > closureMaxArgs && isBoxedName d.name then
        let args ← getParamM! "args"
        let mut i := 0
        xs.forM fun p => do
          let var ← declareIndexVar (←«lean_object*») p.x
          let value ← mkArrayAccess args $ ← mkConstant (← size_t) i.toUInt64
          mkAssignmentM var value
      else
        xs.forM fun p => do
          let p' ← getParamM! s!"{p.x}" >>= (·.asLValue)
          modify fun s => { s with localVars := s.localVars.insert p.x p' }
      emitFnBody b
    | _ => pure ()

def emitDecl (d : Decl) : CodegenM Unit := do
  let d := d.normalizeIds; -- ensure we don't have gaps in the variable indices
  try
    emitDeclAux d
  catch err =>
    throw s!"{err}\ncompiling:\n{d}"

def emitFns : CodegenM Unit := do
  let env ← getEnv
  let decls := getDecls env
  decls.reverse.forM emitDecl

def main : CodegenM Unit := do
  populateRuntimeTable
  IO.println "start emitting functions declarations"
  emitFnDecls
  IO.println "start emitting functions"
  emitFns
  IO.println "start emitting initialization"
  discard $ getModuleInitializationFunction
  emitMainFnIfNeeded

@[export lean_ir_emit_gccjit]
def emitGccJit (env : Environment) (modName : Name) (filepath : String) : IO Unit := do
  let ctx ← Context.acquire
  ctx.setIntOption IntOption.OptimizationLevel 3
  ctx.setBoolOption BoolOption.DumpInitialGimple true
  let ctx : GccContext := {env := env,  modName := modName, ctx := ctx}
  match ← main.run default |>.run ctx with
  | Except.error err => throw $ IO.userError err
  | Except.ok _ => pure ()
  ctx.ctx.compileToFile OutputKind.ObjectFile filepath
  ctx.ctx.release
  
  
