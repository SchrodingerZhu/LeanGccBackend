
import Lean.Data.HashMap
import Lean.Runtime
import Lean.Compiler.NameMangling
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.Boxing
import Lean.Compiler.IR.ResetReuse
import Lean.Compiler.IR.EmitC
import Lean.Compiler.IR.EmitLLVM

import LeanGccJit.Core
open LeanGccJit.Core

namespace Lean.IR
namespace GccJit
def leanMainFn := "_lean_main"

structure GccContext where
  env          : Environment
  modName      : Name
  mainFn       : FunId := default
  mainParams   : Array Param := #[]
  ctx          : Context

structure State where
  funcMap      : HashMap String Func
  declMap      : HashMap FunId (Func × (Array (LeanGccJit.Core.Param × String)))
  constantMap  : HashMap String RValue
  globalMap    : HashMap String LValue
  structMap    : HashMap String (Struct × Array Field)
  deriving Inhabited

abbrev Error := String

abbrev CodegenM :=
  StateRefT State $ ReaderT GccContext $ ExceptT Error IO

def getCtx : CodegenM Context := read >>= (pure ·.ctx)

def getOrCreateFunction (name : String) (create : CodegenM Func) : CodegenM Func :=  do
  match (← get).funcMap.find? name with
  | some f => pure f
  | none   => do
    let f ← create
    modify fun s => { s with funcMap := s.funcMap.insert name f }
    pure f

def getOrCreateConstant (name : String) (create : CodegenM RValue) : CodegenM RValue :=  do
  match (← get).constantMap.find? name with
  | some rv => pure rv
  | none   => do
    let rv ← create
    modify fun s => { s with constantMap := s.constantMap.insert name rv }
    pure rv

def getOrCreateStruct (name : String)
  (create : CodegenM (Struct × Array Field)) : CodegenM (Struct × Array Field) := do
  match (← get).structMap.find? name with
  | some s => pure s
  | none   => do
    let st ← create
    modify fun s => { s with structMap := s.structMap.insert name st }
    pure st

def getGlobalForLiteral (str: String) (ty: JitType) : CodegenM (LValue × Bool) := do
  match (← get).globalMap.find? str with
  | some v => pure (v, true)
  | none => do
    let ctx ← getCtx
    let counter ← get >>= (pure ·.globalMap.size)
    let v ← ctx.newGlobal none GlobalKind.Internal ty s!"__lean_gccjit_literal_{counter}"
    modify fun s => { s with globalMap := s.globalMap.insert str v }
    pure (v, false)

def getOrCreateGlobal (name : String) (ty : JitType) (kind: GlobalKind := GlobalKind.Internal) (init : Option RValue := none) : CodegenM LValue := do
  match (← get).globalMap.find? name with
  | some v => pure v
  | none  => do
    let ctx ← getCtx
    let v ← ctx.newGlobal none kind ty name
    if let some x := init then
      let _ ← Global.setInitializerRValue v x
      pure ()
    modify fun s => { s with globalMap := s.globalMap.insert name v }
    pure v

def getBuiltinFunc (name : String) : CodegenM Func :=
  getCtx >>= (·.getBuiltinFunction name)

def mkStruct (name : String) (fields : Array Field) : CodegenM (Struct × Array Field) := do
  getOrCreateStruct name do
    let ctx ← getCtx
    let st ← ctx.newStructType none name fields
    pure ⟨ st , fields ⟩

def «size_t» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.SizeT)
def «void» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Void)
def «void*» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.VoidPtr)
def «uint8_t» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.UInt8)
def «uint16_t» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.UInt16)
def «uint32_t» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.UInt32)
def «uint64_t» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.UInt64)
def «int» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Int)
def «int8_t» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Int8)
def «int16_t» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Int16)
def «int32_t» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Int32)
def «unsigned» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.UnsignedInt)
def «long» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Long)
def «bool» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Bool)
def «double» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Double)
def «char» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.Char)
def «const char*» : CodegenM JitType := getCtx >>= (·.getType TypeEnum.ConstCharPtr)

def errorField : CodegenM Field := do
  getCtx >>= (·.newField none (← void) "_error")

def getField! (fields : Array Field) (x : Nat) : CodegenM Field := do
  fields.map pure |>.getD x errorField

class AsRValue (α : Type) where
  asRValue : α → CodegenM RValue

instance : AsRValue RValue := ⟨pure⟩
instance : AsRValue LValue := ⟨(·.asRValue)⟩
instance : AsRValue LeanGccJit.Core.Param := ⟨(·.asRValue)⟩

class AsLValue (α : Type) where
  asLValue : α → CodegenM LValue

instance : AsLValue LValue := ⟨pure⟩
instance : AsLValue LeanGccJit.Core.Param := ⟨(·.asLValue)⟩

export AsRValue (asRValue)
export AsLValue (asLValue)

def field (ty : JitType) (name : String) : CodegenM Field := do
  let ctx ← getCtx
  ctx.newField none ty name

def bitfield (ty : JitType) (size : Nat) (name : String) : CodegenM Field := do
  let ctx ← getCtx
  ctx.newBitField none ty size name

def arrayField (ty : JitType) (size : Nat) (name : String) : CodegenM Field := do
  field (← getCtx >>= (·.newArrayType none ty size)) name

def constantOne (x : JitType) : CodegenM RValue :=
  getCtx >>= (do ·.one x)

def constantZero (x : JitType) : CodegenM RValue :=
  getCtx >>= (do ·.zero x)

def mkConstant (x : JitType) (val : UInt64) : CodegenM RValue :=
  getCtx >>= (do ·.newRValueFromUInt64 x val)

def cast [AsRValue τ] (x : τ) (ty : JitType) : CodegenM RValue :=
  getCtx >>= (do ·.newCast none (← asRValue x) ty)

infix:50 " ::: " => cast

def bitcast [AsRValue τ] (x : τ) (ty : JitType) : CodegenM RValue :=
  getCtx >>= (do ·.newBitCast none (← asRValue x) ty)

infix:50 " ::! " => bitcast

def callArray (f: Func) (args: Array RValue) : CodegenM RValue := do
  getCtx >>= (do ·.newCall none f args)

class GccJitCall (α : Type) where
  call : Func → α → CodegenM RValue

instance : GccJitCall Unit where
  call f _ := getCtx >>= (do ·.newCall none f #[])

instance [AsRValue τ] : GccJitCall τ where
  call f x := getCtx >>= (do ·.newCall none f #[(← asRValue x)])

instance [AsRValue a] [AsRValue b] : GccJitCall (a × b) where
  call f x := do
    getCtx >>= (·.newCall none f #[(← asRValue x.1), (← asRValue x.2)])

instance [AsRValue a] [AsRValue b] [AsRValue c] : GccJitCall (a × b × c) where
  call f x := do
    getCtx >>= (·.newCall none f #[(← asRValue x.1), (← asRValue x.2.1), (← asRValue x.2.2)])

instance [AsRValue a] [AsRValue b] [AsRValue c] [AsRValue d] : GccJitCall (a × b × c × d) where
  call f x := do
    getCtx >>= (·.newCall none f #[(← asRValue x.1), (← asRValue x.2.1), (← asRValue x.2.2.1), (← asRValue x.2.2.2)])

export GccJitCall (call)

def binaryOp [AsRValue τ] [AsRValue η] (op: BinaryOp) (x : τ) (y : η) (ty : Option JitType := none) : CodegenM RValue := do
  let x ← asRValue x
  let y ← asRValue y
  let ctx ← getCtx
  let ty ← match ty with
    | some ty => pure ty
    | none    => x.getType
  ctx.newBinaryOp none op ty x y

instance [AsRValue τ] [AsRValue η] : HAdd τ η (CodegenM RValue) where
  hAdd x y := do binaryOp BinaryOp.Plus (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HSub τ η (CodegenM RValue) where
  hSub x y := do binaryOp BinaryOp.Minus (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HMul τ η (CodegenM RValue) where
  hMul x y := do binaryOp BinaryOp.Mult (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HDiv τ η (CodegenM RValue) where
  hDiv x y := do binaryOp BinaryOp.Divide (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HMod τ η (CodegenM RValue) where
  hMod x y := do binaryOp BinaryOp.Divide (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HShiftLeft τ η (CodegenM RValue) where
  hShiftLeft x y := do binaryOp BinaryOp.LShift (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HShiftRight τ η (CodegenM RValue) where
  hShiftRight x y := do binaryOp BinaryOp.RShift (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HAnd τ η (CodegenM RValue) where
  hAnd x y := do binaryOp BinaryOp.BitwiseAnd (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HOr τ η (CodegenM RValue) where
  hOr x y := do binaryOp BinaryOp.BitwiseOr (← asRValue x) (← asRValue y)

instance [AsRValue τ] [AsRValue η] : HXor τ η (CodegenM RValue) where
  hXor x y := do binaryOp BinaryOp.BitwiseXor (← asRValue x) (← asRValue y)

class GccJitCompare (α : Type) (β : Type) where
  compare : Comparison → α → β → CodegenM RValue

instance [AsRValue τ] [AsRValue η] : GccJitCompare τ η where
  compare op x y := getCtx >>= (do ·.newComparison none op (← asRValue x) (← asRValue y))

instance [AsRValue τ] : GccJitCompare τ UInt64 where
  compare op x y := do
    let x' ← asRValue x
    getCtx >>= (do ·.newComparison none  op x' (← mkConstant (← x'.getType) y))

export GccJitCompare (compare)

infix:50 " === " => compare Comparison.EQ
infix:50 " =/= " => compare Comparison.NE
infix:50 " <<· "  => compare Comparison.LT
infix:50 " <== " => compare Comparison.LE
infix:50 " ·>> "  => compare Comparison.GT
infix:50 " >== " => compare Comparison.GE


instance [AsRValue τ] : HAdd τ UInt64 (CodegenM RValue) where
  hAdd x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.Plus x' (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HSub τ UInt64 (CodegenM RValue) where
  hSub x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.Minus x (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HMul τ UInt64 (CodegenM RValue) where
  hMul x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.Mult x (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HDiv τ UInt64 (CodegenM RValue) where
  hDiv x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.Divide x (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HMod τ UInt64 (CodegenM RValue) where
  hMod x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.Modulo x (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HShiftLeft τ UInt64 (CodegenM RValue) where
  hShiftLeft x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.LShift x (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HShiftRight τ UInt64 (CodegenM RValue) where
  hShiftRight x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.RShift x (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HAnd τ UInt64 (CodegenM RValue) where
  hAnd x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.BitwiseAnd x (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HOr τ UInt64 (CodegenM RValue) where
  hOr x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.BitwiseOr x (← mkConstant (← x'.getType) y)

instance [AsRValue τ] : HXor τ UInt64 (CodegenM RValue) where
  hXor x y := do
    let x' ← asRValue x
    binaryOp BinaryOp.BitwiseXor x (← mkConstant (← x'.getType) y)

def mkIfBranch [AsRValue τ] (blk : Block) (cond: τ)
  (then_ : Block → CodegenM Unit)
  (else_ : Block → CodegenM Unit)
  (then_name : Option String := none)
  (else_name : Option String := none)
: CodegenM Unit := do
  let func ← blk.getFunction
  let onTrue ← func.newBlock then_name
  let onFalse ← func.newBlock else_name
  blk.endWithConditional none (← asRValue cond) onTrue onFalse
  then_ onTrue
  else_ onFalse


def likely [AsRValue τ] (x : τ) : CodegenM RValue := do
  let long ← «long»
  let one ← constantOne long
  let x ← cast x long
  let res ← call (← getBuiltinFunc "__builtin_expect") (x, one)
  cast res (← bool)

def unlikely [AsRValue τ] (x : τ) : CodegenM RValue := do
  let long ← «long»
  let zero ← constantZero long
  let x ← cast x long
  let res ← call (← getBuiltinFunc "__builtin_expect") (x, zero)
  cast res (← bool)

def mkFunction
  (name : String)
  (retTy : JitType)
  (params : Array (JitType × String))
  (body: Block → Array LeanGccJit.Core.Param → CodegenM Unit)
  (kind : FunctionKind := FunctionKind.Internal)
  : CodegenM Func := getOrCreateFunction name do
    let ctx ← getCtx
    let params' ← params.mapM fun (ty, name) => do ctx.newParam none ty name
    let func ← ctx.newFunction none kind retTy name params' false
    match kind with
    | FunctionKind.Imported =>
      return func
    | _ => do
      let block ← func.newBlock "entry"
      body block params'
      pure func

def importFunction (name: String) (ret: JitType) (params: Array (JitType × String)) : CodegenM Func :=
  mkFunction name ret params (fun _ _ => pure ()) FunctionKind.Imported

def getParam! (params : Array LeanGccJit.Core.Param) (x : Nat) : CodegenM LeanGccJit.Core.Param := do
  match params.get? x with
  | some p => pure p
  | none   => throw "getParam!: index out of bounds"

def mkLocalVar (blk : Block)  (ty : JitType) (name : String) : CodegenM LValue := do
  let func ← blk.getFunction
  func.newLocal none ty name

def mkReturn [AsRValue τ] (blk : Block) (x : τ) : CodegenM Unit := do
  asRValue x >>= (blk.endWithReturn none ·)

def mkAssignment [AsLValue α] [AsRValue τ] (blk : Block) (x : α) (y : τ) : CodegenM Unit := do
  blk.addAssignment none (← asLValue x) (← asRValue y)

def mkAssignmentOp [AsLValue α] [AsRValue τ] (blk : Block) (op : BinaryOp) (x : α) (y : τ) : CodegenM Unit := do
  blk.addAssignmentOp none (← asLValue x) op (← asRValue y)

def mkEval [AsRValue τ] (blk : Block) (x : τ) : CodegenM Unit := do
  blk.addEval none (← asRValue x)

def mkArrayAccess [AsRValue α] [AsRValue τ] (x : α) (y : τ) : CodegenM LValue := do
  getCtx >>= (·.newArrayAccess none (← asRValue x) (← asRValue y))

def arrayToPtr [AsRValue α] (x : α) : CodegenM RValue := do
  let x ← asRValue x
  let elem ← mkArrayAccess x (← constantZero (← size_t))
  elem.getAddress none

def mkWhileLoop
  (blk : Block)
  (cond : RValue)
  (body : Block → CodegenM Unit)
  (after : Block → CodegenM Unit) : CodegenM Unit := do
  let func ← blk.getFunction
  let bodyBlock ← func.newBlock none
  let afterBlock ← func.newBlock none
  blk.endWithConditional none cond bodyBlock afterBlock
  body bodyBlock
  bodyBlock.endWithConditional none cond bodyBlock afterBlock
  after afterBlock

class GccJitUnary (α : Type) where
  unary : UnaryOp → α → CodegenM RValue

instance [AsRValue τ] : GccJitUnary τ where
  unary op x := do
    let x ← asRValue x
    getCtx >>= (·.newUnaryOp none op (← x.getType) x)

export GccJitUnary (unary)

prefix:20 " ·-· " => unary UnaryOp.Minus
prefix:20 " ·~· " => unary UnaryOp.BitwiseNegate
prefix:20 " ·!· " => unary UnaryOp.LogicalNegate

def dereferenceField [AsRValue α] (x : α) (structTy : Struct × Array Field) (idx : Nat) : CodegenM LValue := do
  let x ← asRValue x
  x.dereferenceField none (← getField! structTy.2 idx)

def dereference  [AsRValue α] (x : α) : CodegenM LValue := do
  let x ← asRValue x
  x.dereference none
