import LeanGccBackend.Basic
import LeanGccJit.Core

open LeanGccJit.Core
namespace Lean.IR
namespace GccJit

def getLeanObject : CodegenM (Struct × Array Field) :=
  getOrCreateStruct "lean_object" do
    let ctx ← getCtx
    let int ← ctx.getType TypeEnum.Int
    let unsigned ← ctx.getType TypeEnum.UnsignedInt
    let m_rc ← ctx.newField none int "m_rc"
    let m_cs_sz ← ctx.newBitField none unsigned 16 "m_cs_sz"
    let m_other ← ctx.newBitField none unsigned 8 "m_other"
    let m_tag ← ctx.newBitField none unsigned 8 "m_tag"
    let obj ← ctx.newStructType none "lean_object" #[m_rc, m_cs_sz, m_other, m_tag]
    pure (obj, #[m_rc, m_cs_sz, m_other, m_tag])

def getLeanObjPtr : CodegenM JitType :=
  getLeanObject >>= (·.fst.asJitType) >>= (·.getPointer)

def getLeanBox : CodegenM Func :=
  getOrCreateFunction "lean_box" do
    let ctx ← getCtx
    let obj ← getLeanObjPtr
    let size_t ← ctx.getType TypeEnum.SizeT
    let input ← ctx.newParam none size_t "value"
    let leanBox ← ctx.newFunction none FunctionKind.AlwaysInline obj "lean_box" #[input] false
    let block ← leanBox.newBlock "entry"
    let one ← ctx.one size_t
    let shifted ← ctx.newBinaryOp none BinaryOp.LShift size_t (← input.asRValue) one
    let set ← ctx.newBinaryOp none BinaryOp.BitwiseOr size_t shifted one
    let casted ← ctx.newBitCast none set obj
    block.endWithReturn none casted
    pure leanBox

def getLeanUnbox : CodegenM Func :=
  getOrCreateFunction "lean_unbox" do
    let ctx ← getCtx
    let obj ← getLeanObjPtr
    let size_t ← ctx.getType TypeEnum.SizeT
    let input ← ctx.newParam none obj "boxed"
    let leanUnbox ← ctx.newFunction none FunctionKind.AlwaysInline obj "lean_unbox" #[input] false
    let block ← leanUnbox.newBlock "entry"
    let casted ← ctx.newBitCast none (← input.asRValue) size_t
    let shifted ← ctx.newBinaryOp none BinaryOp.RShift size_t casted (← ctx.one size_t)
    block.endWithReturn none shifted
    pure leanUnbox

def getLeanIsScalar : CodegenM Func := 
  getOrCreateFunction "lean_is_scalar" do
    let ctx ← getCtx
    let obj ← getLeanObjPtr
    let bool ← ctx.getType TypeEnum.Bool
    let input ← ctx.newParam none obj "obj"
    let leanIsScalar ← ctx.newFunction none FunctionKind.AlwaysInline bool "lean_is_scalar" #[input] false
    let block ← leanIsScalar.newBlock "entry"
    let casted ← ctx.newBitCast none (← input.asRValue) (← ctx.getType TypeEnum.SizeT)
    let one ← ctx.one (← ctx.getType TypeEnum.SizeT)
    let bitand ← ctx.newBinaryOp none BinaryOp.BitwiseAnd (← ctx.getType TypeEnum.SizeT) casted one
    let cmp ← ctx.newComparison none Comparison.EQ bitand one
    block.endWithReturn none cmp
    pure leanIsScalar

def importFunction (name: String) (ret: JitType) (params: Array (String × JitType)) : CodegenM Func :=
  getOrCreateFunction name do
    let ctx ← getCtx
    let mut inputs := #[]
    for (name, ty) in params do
      inputs := inputs.push (← ctx.newParam none ty name)
    ctx.newFunction none FunctionKind.Imported ret name inputs false

def getLeanMarkPersistent : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  let obj ← getLeanObjPtr
  importFunction "lean_mark_persistent" void #[("obj", obj)]

def getLeanAllocSmall : CodegenM Func := do
  let ctx ← getCtx
  let voidPtr ← ctx.getType TypeEnum.VoidPtr
  let unsigned ← ctx.getType TypeEnum.UnsignedInt
  importFunction "lean_alloc_small" voidPtr #[("sz", unsigned), ("slot_idx", unsigned)]

def getLeanFreeSmall : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  let voidPtr ← ctx.getType TypeEnum.VoidPtr
  importFunction "lean_free_small" void #[("p", voidPtr)]

def getLeanSmallMemSize : CodegenM Func := do
  let ctx ← getCtx
  let unsigned ← ctx.getType TypeEnum.UnsignedInt
  let voidPtr ← ctx.getType TypeEnum.VoidPtr
  importFunction "lean_small_mem_size" unsigned #[("p", voidPtr)]

def getLeanIncHeartbeat : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  importFunction "lean_inc_heartbeat" void #[]

def callLeanBox (value : RValue) : CodegenM RValue := do
  let ctx ← getCtx
  let leanBox ← getLeanBox
  ctx.newCall none leanBox #[value]

def callLeanMarkPersistent (obj : RValue) : CodegenM RValue := do
  let ctx ← getCtx
  let leanMarkPersistent ← getLeanMarkPersistent
  ctx.newCall none leanMarkPersistent #[obj]
