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
    let fields := #[m_rc, m_cs_sz, m_other, m_tag]
    let obj ← ctx.newStructType none "lean_object" fields
    pure (obj, fields)

def getLeanObjPtr : CodegenM JitType :=
  getLeanObject >>= (·.fst.asJitType) >>= (·.getPointer)

def getLeanArrayObject : CodegenM (Struct × Array Field) :=
  getOrCreateStruct "lean_array_object" do
    let ctx ← getCtx
    let obj ← getLeanObject >>= (·.fst.asJitType)
    let objPtr ← getLeanObjPtr
    let size_t ← ctx.getType TypeEnum.SizeT
    let m_header ← ctx.newField none obj "m_header"
    let m_size ← ctx.newField none size_t "m_size"
    let m_capacity ← ctx.newField none size_t "m_capacity"
    let zero_array ← ctx.newArrayType none objPtr 0
    let m_data ← ctx.newField none zero_array "m_data"
    let fields := #[m_header, m_size, m_capacity, m_data]
    let array ← ctx.newStructType none "lean_array_object" fields
    pure (array, fields)

def getLeanSArrayObject : CodegenM (Struct × Array Field) :=
  getOrCreateStruct "lean_sarray_object" do
    let ctx ← getCtx
    let obj ← getLeanObject >>= (·.fst.asJitType)
    let uint8_t ← ctx.getType TypeEnum.UInt8
    let size_t ← ctx.getType TypeEnum.SizeT
    let m_header ← ctx.newField none obj "m_header"
    let m_size ← ctx.newField none size_t "m_size"
    let m_capacity ← ctx.newField none size_t "m_capacity"
    let zero_array ← ctx.newArrayType none uint8_t 0
    let m_data ← ctx.newField none zero_array "m_data"
    let fields := #[m_header, m_size, m_capacity, m_data]
    let array ← ctx.newStructType none "lean_sarray_object" fields
    pure (array, fields)

def getLeanStringObject : CodegenM (Struct × Array Field) :=
  getOrCreateStruct "lean_string_object" do
    let ctx ← getCtx
    let obj ← getLeanObject >>= (·.fst.asJitType)
    let char ← ctx.getType TypeEnum.Char
    let size_t ← ctx.getType TypeEnum.SizeT
    let m_header ← ctx.newField none obj "m_header"
    let m_size ← ctx.newField none size_t "m_size"
    let m_capacity ← ctx.newField none size_t "m_capacity"
    let m_length ← ctx.newField none size_t "m_length"
    let zero_array ← ctx.newArrayType none char 0
    let m_data ← ctx.newField none zero_array "m_data"
    let fields := #[m_header, m_size, m_capacity, m_length, m_data]
    let string ← ctx.newStructType none "lean_string_object" fields
    pure (string, fields)

def getLeanClosureObject : CodegenM (Struct × Array Field) :=
  getOrCreateStruct "lean_closure_object" do
    let ctx ← getCtx
    let obj ← getLeanObject >>= (·.fst.asJitType)
    let objPtr ← getLeanObjPtr
    let uint16_t ← ctx.getType TypeEnum.UInt16
    let voidPtr ← ctx.getType TypeEnum.VoidPtr
    let m_header ← ctx.newField none obj "m_header"
    let m_fun ← ctx.newField none voidPtr "m_fun"
    let m_arity ← ctx.newField none uint16_t "m_arity"
    let m_num_fixed ← ctx.newField none uint16_t "m_num_fixed"
    let zero_array ← ctx.newArrayType none objPtr 0
    let m_objs ← ctx.newField none zero_array "m_objs"
    let fields := #[m_header, m_fun, m_arity, m_num_fixed, m_objs]
    let closure ← ctx.newStructType none "lean_closure_object" fields
    pure (closure, fields)

-- TODO: lean_ref_object / lean_task / lean_task_imp;

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

-- TODO: lean_register_external_class (currently no needed)

def getLeanSetExitOnPanic : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  let bool ← ctx.getType TypeEnum.Bool
  importFunction "lean_set_exit_on_panic" void #[("flag", bool)]

def getLeanSetPanicMessages : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  let bool ← ctx.getType TypeEnum.Bool
  importFunction "lean_set_panic_messages" void #[("flag", bool)]

def getLeanPanicFn : CodegenM Func := do
  let objPtr ← getLeanObjPtr
  importFunction "lean_panic_fn" objPtr #[("default_val", objPtr), ("msg", objPtr)]

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

def getLeanInternalPanic : CodegenM Func := do
  let ctx ← getCtx
  let constCharPtr ← ctx.getType TypeEnum.ConstCharPtr
  let void ← ctx.getType TypeEnum.Void
  importFunction "lean_internal_panic" void #[("msg", constCharPtr)]

def getLeanPanicOutOfMemory : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  importFunction "lean_panic_out_of_memory" void #[]

def getLeanPanicUnreachable : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  importFunction "lean_panic_unreachable" void #[]

def getLeanPanicRcOverflow : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  importFunction "lean_panic_rc_overflow" void #[]

def getLeanAlign : CodegenM Func := 
  getOrCreateFunction "lean_align" do
    let ctx ← getCtx
    let size_t ← ctx.getType TypeEnum.SizeT
    let v ← ctx.newParam none size_t "v"
    let a ← ctx.newParam none size_t "a"
    let leanAlign ← ctx.newFunction none FunctionKind.AlwaysInline size_t "lean_align" #[v, a] false
    let block ← leanAlign.newBlock "entry"
    -- Calculate the assignment with: v + ((-v) & (a - 1))
    let v' ← v.asRValue
    let negV ← ctx.newUnaryOp none UnaryOp.Minus size_t v'
    let one ← ctx.one size_t
    let aMinusOne ← ctx.newBinaryOp none BinaryOp.Minus size_t (← a.asRValue) one
    let bitand ← ctx.newBinaryOp none BinaryOp.BitwiseAnd size_t negV aMinusOne
    let result ← ctx.newBinaryOp none BinaryOp.Plus size_t v' bitand
    block.endWithReturn none result
    pure leanAlign

def Constant.LEAN_OBJECT_SIZE_DELTA : CodegenM RValue :=
  getOrCreateConstant "LEAN_OBJECT_SIZE_DELTA" do
    let ctx ← getCtx
    let size_t ← ctx.getType TypeEnum.SizeT
    ctx.newRValueFromUInt64 size_t 8

def Constant.SIZE_T_SIZE : CodegenM RValue :=
  getOrCreateConstant "LEAN_OBJECT_SIZE_DELTA" do
    let ctx ← getCtx
    let size_t ← ctx.getType TypeEnum.SizeT
    let sizeTSize ← size_t.getSize
    ctx.newRValueFromUInt64 size_t sizeTSize.toUInt64

def getLeanGetSlotIdx : CodegenM Func := 
  getOrCreateFunction "lean_get_slot_idx" do
    let ctx ← getCtx
    let unsigned ← ctx.getType TypeEnum.UnsignedInt
    let sz ← ctx.newParam none unsigned "sz"
    let leanGetSlotIdx ← ctx.newFunction none FunctionKind.AlwaysInline unsigned "lean_get_slot_idx" #[sz] false
    let block ← leanGetSlotIdx.newBlock "entry"
    let one ← ctx.one unsigned
    let size_t ← ctx.getType TypeEnum.SizeT
    let div ← ctx.newBinaryOp none BinaryOp.Divide unsigned 
      (← sz.asRValue >>= (ctx.newCast none · size_t)) (← Constant.LEAN_OBJECT_SIZE_DELTA)
    let minusOne ← ctx.newBinaryOp none BinaryOp.Minus unsigned div one
    block.endWithReturn none minusOne
    pure leanGetSlotIdx

-- Assumption: SMALL_ALLOCATOR is always used
def getLeanAllocSmallObject : CodegenM Func :=
  getOrCreateFunction "lean_alloc_small_object" do
    let ctx ← getCtx
    let objPtr ← getLeanObjPtr
    let unsigned ← ctx.getType TypeEnum.UnsignedInt
    let size_t ← ctx.getType TypeEnum.SizeT
    let sz ← ctx.newParam none unsigned "sz"
    let leanAllocSmallObject ← ctx.newFunction none FunctionKind.AlwaysInline objPtr "lean_alloc_small_object" #[sz] false
    let block ← leanAllocSmallObject.newBlock "entry"
    let alignedSz ← ctx.newCall none (← getLeanAlign) 
      #[(← sz.asRValue >>= (ctx.newCast none · size_t)), (← Constant.LEAN_OBJECT_SIZE_DELTA)]
    let alignedSz ← ctx.newCast none alignedSz unsigned
    let slot ← ctx.newCall none (← getLeanGetSlotIdx) #[alignedSz]
    let memory ← ctx.newCall none (← getLeanAllocSmall) #[alignedSz, slot]
    let obj ← ctx.newCast none memory objPtr
    block.endWithReturn none obj
    pure leanAllocSmallObject

def getLeanAllocCtorMemory : CodegenM Func :=
  getOrCreateFunction "lean_alloc_ctor_memory" do
    let ctx ← getCtx
    let objPtr ← getLeanObjPtr
    let unsigned ← ctx.getType TypeEnum.UnsignedInt
    let size_t ← ctx.getType TypeEnum.SizeT
    let sz ← ctx.newParam none unsigned "sz"
    let leanAllocCtorMemory ← ctx.newFunction none FunctionKind.AlwaysInline objPtr "lean_alloc_ctor_memory" #[sz] false
    let block ← leanAllocCtorMemory.newBlock "entry"
    let alignedSz' ← ctx.newCall none (← getLeanAlign) 
      #[(← sz.asRValue >>= (ctx.newCast none · size_t)), (← Constant.LEAN_OBJECT_SIZE_DELTA)]
    let alignedSz ← ctx.newCast none alignedSz' unsigned
    let slot ← ctx.newCall none (← getLeanGetSlotIdx) #[(← ctx.newCast none alignedSz unsigned)]
    let memory ← ctx.newCall none (← getLeanAllocSmall) #[alignedSz, slot]
    let obj ← ctx.newCast none memory objPtr
    let hasAlignOffset ← ctx.newComparison none Comparison.GT alignedSz (← sz.asRValue)
    let onTrue ← leanAllocCtorMemory.newBlock "on_true"
    let onFalse ← leanAllocCtorMemory.newBlock "on_false"
    block.endWithConditional none hasAlignOffset onTrue onFalse
    onFalse.endWithReturn none obj
    -- assign last word to be NULL
    let sizeTPtr ← size_t.getPointer
    let zero ← ctx.zero size_t
    let length ← ctx.newBinaryOp none BinaryOp.Divide unsigned alignedSz' (← Constant.SIZE_T_SIZE)
    let offset ← ctx.newBinaryOp none BinaryOp.Minus unsigned length (← ctx.one unsigned)
    let access ← ctx.newArrayAccess none (← ctx.newCast none memory sizeTPtr) offset
    onTrue.addAssignment none access zero
    onTrue.endWithReturn none obj
    pure leanAllocCtorMemory

def getLeanSmallObjectSize : CodegenM Func :=
  getOrCreateFunction "lean_small_object_size" do
    let ctx ← getCtx
    let voidPtr ← ctx.getType TypeEnum.VoidPtr
    let objPtr ← getLeanObjPtr
    let o ← ctx.newParam none objPtr "o"
    let unsigned ← ctx.getType TypeEnum.UnsignedInt
    let leanSmallObjectSize ← ctx.newFunction none FunctionKind.AlwaysInline unsigned "lean_small_object_size" #[o] false
    let block ← leanSmallObjectSize.newBlock "entry"
    let casted ← ctx.newBitCast none (← o.asRValue) voidPtr
    let size ← ctx.newCall none (← getLeanSmallMemSize) #[casted]
    block.endWithReturn none size
    pure leanSmallObjectSize

def getLeanFreeSmallObject : CodegenM Func :=
  getOrCreateFunction "lean_free_small_object" do
    let ctx ← getCtx
    let void ← ctx.getType TypeEnum.Void
    let objPtr ← getLeanObjPtr
    let o ← ctx.newParam none objPtr "o"
    let leanFreeSmallObject ← ctx.newFunction none FunctionKind.AlwaysInline void "lean_free_small_object" #[o] false
    let block ← leanFreeSmallObject.newBlock "entry"
    let casted ← ctx.newBitCast none (← o.asRValue) (← ctx.getType TypeEnum.VoidPtr)
    let call ← ctx.newCall none (← getLeanFreeSmall) #[casted]
    block.addEval none call
    block.endWithVoidReturn none
    pure leanFreeSmallObject

def getLeanAllocObject : CodegenM Func := do
  let ctx ← getCtx
  let size_t ← ctx.getType TypeEnum.SizeT
  importFunction "lean_alloc_object" (← getLeanObjPtr) #[("sz", size_t)]

def getLeanFreeObject : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  let objPtr ← getLeanObjPtr
  importFunction "lean_free_object" void #[("o", objPtr)]

def getLeanPtrTag : CodegenM Func :=
  getOrCreateFunction "lean_ptr_tag" do
    let ctx ← getCtx
    let uint8_t ← ctx.getType TypeEnum.UInt8
    let (obj, fields) ← getLeanObject
    let objPtr ← obj.asJitType >>= (·.getPointer)
    let o ← ctx.newParam none objPtr "o"
    let leanPtrTag ← ctx.newFunction none FunctionKind.AlwaysInline uint8_t "lean_ptr_tag" #[o] false
    let block ← leanPtrTag.newBlock "entry"
    let m_tag := fields.getD 3 (← errorField)
    let access ← o.asRValue >>= (·.dereferenceField none $ m_tag) >>= (·.asRValue)
    block.endWithReturn none access
    pure leanPtrTag

def getLeanPtrOther : CodegenM Func :=
  getOrCreateFunction "lean_ptr_other" do
    let ctx ← getCtx
    let uint8_t ← ctx.getType TypeEnum.UInt8
    let (obj, fields) ← getLeanObject
    let objPtr ← obj.asJitType >>= (·.getPointer)
    let o ← ctx.newParam none objPtr "o"
    let leanPtrOther ← ctx.newFunction none FunctionKind.AlwaysInline uint8_t "lean_ptr_other" #[o] false
    let block ← leanPtrOther.newBlock "entry"
    let m_other := fields.getD 2 (← errorField)
    let access ← o.asRValue >>= (·.dereferenceField none $ m_other) >>= (·.asRValue)
    block.endWithReturn none access
    pure leanPtrOther

def getLeanObjectByteSize : CodegenM Func :=
  getOrCreateFunction "lean_object_byte_size" do
    let ctx ← getCtx
    let size_t ← ctx.getType TypeEnum.SizeT
    let objPtr ← getLeanObjPtr
    importFunction "lean_object_byte_size" size_t #[("o", objPtr)]

def getLeanIsMT : CodegenM Func := 
  getOrCreateFunction "lean_is_mt" do
    let ctx ← getCtx
    let bool ← ctx.getType TypeEnum.Bool
    let (obj, fields) ← getLeanObject
    let objPtr ← obj.asJitType >>= (·.getPointer)
    let o ← ctx.newParam none objPtr "o"
    let leanIsMT ← ctx.newFunction none FunctionKind.AlwaysInline bool "lean_is_mt" #[o] false
    let block ← leanIsMT.newBlock "entry"
    let m_rc := fields.getD 0 (← errorField)
    let access ← o.asRValue >>= (·.dereferenceField none $ m_rc) >>= (·.asRValue)
    let cmp ← ctx.newComparison none Comparison.LT access (← ctx.zero (← ctx.getType TypeEnum.Int))
    block.endWithReturn none cmp
    pure leanIsMT

def getLeanIsST : CodegenM Func := 
  getOrCreateFunction "lean_is_st" do
    let ctx ← getCtx
    let bool ← ctx.getType TypeEnum.Bool
    let (obj, fields) ← getLeanObject
    let objPtr ← obj.asJitType >>= (·.getPointer)
    let o ← ctx.newParam none objPtr "o"
    let leanIsST ← ctx.newFunction none FunctionKind.AlwaysInline bool "lean_is_st" #[o] false
    let block ← leanIsST.newBlock "entry"
    let m_rc := fields.getD 0 (← errorField)
    let access ← o.asRValue >>= (·.dereferenceField none $ m_rc) >>= (·.asRValue)
    let cmp ← ctx.newComparison none Comparison.GT access (← ctx.zero (← ctx.getType TypeEnum.Int))
    block.endWithReturn none cmp
    pure leanIsST

def getLeanIsPersistent : CodegenM Func := 
  getOrCreateFunction "lean_is_persistent" do
    let ctx ← getCtx
    let bool ← ctx.getType TypeEnum.Bool
    let (obj, fields) ← getLeanObject
    let objPtr ← obj.asJitType >>= (·.getPointer)
    let o ← ctx.newParam none objPtr "o"
    let leanIsPersistent ← ctx.newFunction none FunctionKind.AlwaysInline bool "lean_is_persistent" #[o] false
    let block ← leanIsPersistent.newBlock "entry"
    let m_rc := fields.getD 0 (← errorField)
    let access ← o.asRValue >>= (·.dereferenceField none $ m_rc) >>= (·.asRValue)
    let cmp ← ctx.newComparison none Comparison.EQ access (← ctx.zero (← ctx.getType TypeEnum.Int))
    block.endWithReturn none cmp
    pure leanIsPersistent

def getLeanIncRefCold : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  let objPtr ← getLeanObjPtr
  importFunction "lean_inc_ref_cold" void #[("o", objPtr)]

def getLeanIncRefNCold : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  let objPtr ← getLeanObjPtr
  let unsigned ← ctx.getType TypeEnum.UnsignedInt
  importFunction "lean_inc_ref_n_cold" void #[("o", objPtr), ("n", unsigned)]

def getLeanIncRef : CodegenM Func := 
  getOrCreateFunction "lean_inc_ref" do
    let ctx ← getCtx
    let void ← ctx.getType TypeEnum.Void
    let (obj, fields) ← getLeanObject
    let objPtr ← obj.asJitType >>= (·.getPointer)
    let o ← ctx.newParam none objPtr "o"
    let leanIncRef ← ctx.newFunction none FunctionKind.AlwaysInline void "lean_inc_ref" #[o] false
    let block ← leanIncRef.newBlock "entry"
    let o' ← o.asRValue
    let isSt ← ctx.newCall none (← getLeanIsST) #[o'] >>= likely
    let onTrue ← leanIncRef.newBlock "on_true"
    let onFalse ← leanIncRef.newBlock "on_false"
    block.endWithConditional none isSt onTrue onFalse
    let m_rc := fields.getD 0 (← errorField)
    let access ← o'.dereferenceField none $ m_rc
    -- On true, o->m_rc += 1;
    let one ← ctx.one (← ctx.getType TypeEnum.Int)
    onTrue.addAssignmentOp none access BinaryOp.Plus one
    onTrue.endWithVoidReturn none
    -- On false, check m_rc != 0
    let cmp ← ctx.newComparison none Comparison.NE (← access.asRValue) (← ctx.zero (← ctx.getType TypeEnum.Int))
    let onPersistent ← leanIncRef.newBlock "persistent"
    let onNotPersistent ← leanIncRef.newBlock "not_persistent"
    onFalse.endWithConditional none cmp onNotPersistent onPersistent
    -- On not persistent, call lean_inc_ref_cold(o);
    let call ← ctx.newCall none (← getLeanIncRefCold) #[o']
    onNotPersistent.addEval none call
    onNotPersistent.endWithVoidReturn none
    -- On persistent, do nothing
    onPersistent.endWithVoidReturn none
    pure leanIncRef

def getLeanIncRefN : CodegenM Func := 
  getOrCreateFunction "lean_inc_ref_n" do
    let ctx ← getCtx
    let void ← ctx.getType TypeEnum.Void
    let (obj, fields) ← getLeanObject
    let objPtr ← obj.asJitType >>= (·.getPointer)
    let o ← ctx.newParam none objPtr "o"
    let n ← ctx.newParam none (← ctx.getType TypeEnum.SizeT) "n"
    let int ← ctx.getType TypeEnum.Int
    let unsigned ← ctx.getType TypeEnum.UnsignedInt
    let leanIncRefN ← ctx.newFunction none FunctionKind.AlwaysInline void "lean_inc_ref_n" #[o, n] false
    let block ← leanIncRefN.newBlock "entry"
    let o' ← o.asRValue
    let n' ← n.asRValue
    let isSt ← ctx.newCall none (← getLeanIsST) #[o'] >>= likely
    let onTrue ← leanIncRefN.newBlock "on_true"
    let onFalse ← leanIncRefN.newBlock "on_false"
    block.endWithConditional none isSt onTrue onFalse
    let m_rc := fields.getD 0 (← errorField)
    let access ← o'.dereferenceField none $ m_rc
    -- On true, o->m_rc += n;
    onTrue.addAssignmentOp none access BinaryOp.Plus (← ctx.newCast none n' int)
    onTrue.endWithVoidReturn none
    -- On false, check m_rc != 0
    let cmp ← ctx.newComparison none Comparison.NE (← access.asRValue) (← ctx.zero int)
    let onPersistent ← leanIncRefN.newBlock "persistent"
    let onNotPersistent ← leanIncRefN.newBlock "not_persistent"
    onFalse.endWithConditional none cmp onNotPersistent onPersistent
    -- On not persistent, call lean_inc_ref_cold(o);
    let call ← ctx.newCall none (← getLeanIncRefNCold) #[o', (← ctx.newCast none n' unsigned)]
    onNotPersistent.addEval none call
    onNotPersistent.endWithVoidReturn none
    -- On persistent, do nothing
    onPersistent.endWithVoidReturn none
    pure leanIncRefN

def getLeanDecRefCold : CodegenM Func := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Void
  let objPtr ← getLeanObjPtr
  importFunction "lean_dec_ref_cold" void #[("o", objPtr)]

def getLeanDecRef : CodegenM Func := 
  getOrCreateFunction "lean_dec_ref" do
    let ctx ← getCtx
    let void ← ctx.getType TypeEnum.Void
    let (obj, fields) ← getLeanObject
    let objPtr ← obj.asJitType >>= (·.getPointer)
    let o ← ctx.newParam none objPtr "o"
    let leanDecRef ← ctx.newFunction none FunctionKind.AlwaysInline void "lean_dec_ref" #[o] false
    let block ← leanDecRef.newBlock "entry"
    let o' ← o.asRValue
    let m_rc := fields.getD 0 (← errorField)
    let access ← o'.dereferenceField none $ m_rc
    let one ← ctx.one (← ctx.getType TypeEnum.Int)
    let isNonExclusize ← ctx.newComparison none Comparison.GT (← access.asRValue) one >>= likely
    let nonExclusive ← leanDecRef.newBlock "non_exlucsive"
    let exclusive ← leanDecRef.newBlock "exclusive"
    block.endWithConditional none isNonExclusize nonExclusive exclusive
    -- On non_exlucsive, o->m_rc -= 1;
    nonExclusive.addAssignmentOp none access BinaryOp.Minus one
    nonExclusive.endWithVoidReturn none
    -- On exclusive, check m_rc != 0
    let cmp ← ctx.newComparison none Comparison.NE (← access.asRValue) (← ctx.zero (← ctx.getType TypeEnum.Int))
    let onPersistent ← leanDecRef.newBlock "persistent"
    let onNotPersistent ← leanDecRef.newBlock "not_persistent"
    exclusive.endWithConditional none cmp onNotPersistent onPersistent
    -- On not persistent, call lean_dec_ref_cold(o);
    let call ← ctx.newCall none (← getLeanDecRefCold) #[o']
    onNotPersistent.addEval none call
    onNotPersistent.endWithVoidReturn none
    -- On persistent, do nothing
    onPersistent.endWithVoidReturn none
    pure leanDecRef

private def ifNotScalar (name : String)  (onNotScalar : Block → RValue → CodegenM Unit) (extraParam : Array LeanGccJit.Core.Param := #[]) : CodegenM Func := 
  getOrCreateFunction name do 
    let ctx ← getCtx
    let void ← ctx.getType TypeEnum.Void
    let objPtr ← getLeanObjPtr
    let o ← ctx.newParam none objPtr "o"
    let func ← ctx.newFunction none FunctionKind.AlwaysInline void name (#[o] ++ extraParam) false
    let block ← func.newBlock "entry"
    let o' ← o.asRValue
    let isScalar ← ctx.newCall none (← getLeanIsScalar) #[o']
    let scalar ← func.newBlock "scalar"
    let notScalar ← func.newBlock "not_scalar"
    block.endWithConditional none isScalar scalar notScalar
    scalar.endWithVoidReturn none
    onNotScalar notScalar o'
    notScalar.endWithVoidReturn none
    pure func

def getLeanInc : CodegenM Func := 
  ifNotScalar "lean_inc" fun block o' => 
    getCtx >>= (do ·.newCall none (← getLeanIncRef) #[o']) >>= (block.addEval none ·)

def getLeanIncN : CodegenM Func := do 
  let ctx ← getCtx
  let n ← ctx.newParam none (← ctx.getType TypeEnum.SizeT) "n"
  ifNotScalar "lean_inc_n" (fun block o' => 
    getCtx >>= (do ·.newCall none (← getLeanIncRefN) #[o', (← n.asRValue)]) >>= (block.addEval none ·))
    #[n]


def getLeanDec : CodegenM Func :=
  ifNotScalar "lean_dec" fun block o' => 
    getCtx >>= (do ·.newCall none (← getLeanDecRef) #[o']) >>= (block.addEval none ·)

    
  
    

def callLeanBox (value : RValue) : CodegenM RValue := do
  let ctx ← getCtx
  let leanBox ← getLeanBox
  ctx.newCall none leanBox #[value]

def callLeanMarkPersistent (obj : RValue) : CodegenM RValue := do
  let ctx ← getCtx
  let leanMarkPersistent ← getLeanMarkPersistent
  ctx.newCall none leanMarkPersistent #[obj]
