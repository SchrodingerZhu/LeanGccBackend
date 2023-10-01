import LeanGccBackend.Basic
import LeanGccJit.Core

open LeanGccJit.Core
namespace Lean.IR
namespace GccJit

def getLeanObject : CodegenM (Struct × Array Field) := do
  let unsigned ← unsigned
  mkStruct "lean_object" #[
    (← field (← int) "m_rc"),
    (← bitfield unsigned 16 "m_cs_sz"),
    (← bitfield unsigned 8 "m_other"),
    (← bitfield unsigned 8 "m_tag")
  ]

def «lean_object» : CodegenM JitType :=
  getLeanObject >>= (·.fst.asJitType)

def «lean_object*» : CodegenM JitType :=
  getLeanObject >>= (·.fst.asJitType) >>= (·.getPointer)

def getLeanArrayObject : CodegenM (Struct × Array Field) := do
  let size_t ← size_t
  mkStruct "lean_array_object" #[
    (← field (← lean_object) "m_header"),
    (← field size_t "m_size"),
    (← field size_t "m_capacity"),
    (← arrayField (← «lean_object*») 0 "m_data")
  ]

def getLeanSArrayObject : CodegenM (Struct × Array Field) := do
  let size_t ← size_t
  mkStruct "lean_sarray_object" #[
    (← field (← lean_object) "m_header"),
    (← field size_t "m_size"),
    (← field size_t "m_capacity"),
    (← arrayField (← uint8_t) 0 "m_data")
  ]

def getLeanStringObject : CodegenM (Struct × Array Field) := do
  let size_t ← size_t
  mkStruct "lean_string_object" #[
    (← field (← lean_object) "m_header"),
    (← field size_t "m_size"),
    (← field size_t "m_capacity"),
    (← field size_t "m_length"),
    (← arrayField (← char) 0 "m_data")
  ]

def getLeanClosureObject : CodegenM (Struct × Array Field) := do 
  let uint16_t ← uint16_t
  mkStruct "lean_closure_object" #[
    (←  field (← lean_object) "m_header"),
    (← field (← «void*») "m_fun"),
    (← field uint16_t "m_arity"),
    (← field uint16_t "m_num_fixed"),
    (← arrayField (← «lean_object*») 0 "m_objs")
  ]

-- TODO: lean_ref_object / lean_task / lean_task_imp;

def getLeanBox : CodegenM Func := do
  mkFunction "lean_box" (← «lean_object*») #[((← size_t), "value")] fun blk params => do
    let value ← getParam! params 0
    mkReturn blk $ (←(←(← value <<< (1 : UInt64)) ||| (1 : UInt64)) ::! (←«lean_object*»))

def getLeanUnbox : CodegenM Func := do
  mkFunction "lean_unbox" (← size_t) #[((← «lean_object*»), "value")] fun blk params => do
    let value ← (←getParam! params 0) ::! (← size_t)
    mkReturn blk $ (← value >>> (1 : UInt64))

def getLeanIsScalar : CodegenM Func := do
  mkFunction "lean_is_scalar" (← bool) #[((← «lean_object*»), "obj")] fun blk params => do
    let obj ← (←getParam! params 0) ::! (← size_t)
    mkReturn blk $ (←(←obj &&& (1 : UInt64)) =/= (0 : UInt64))

-- -- TODO: lean_register_external_class (currently no needed)

def getLeanSetExitOnPanic : CodegenM Func := do
  importFunction "lean_set_exit_on_panic" (←void) #[((←bool), "flag")]

def getLeanSetPanicMessages : CodegenM Func := do
  importFunction "lean_set_panic_messages" (←void) #[((←bool), "flag")]

def getLeanPanicFn : CodegenM Func := do
  importFunction "lean_panic_fn" (← «lean_object*») #[
    ((← «lean_object*»), "default_val"), ((← «lean_object*»), "msg")
  ]

def getLeanMarkPersistent : CodegenM Func := do
  importFunction "lean_mark_persistent" (←void) #[((← «lean_object*»), "obj")]

def getLeanAllocSmall : CodegenM Func := do
  let unsigned ← unsigned
  importFunction "lean_alloc_small" (← «lean_object*») #[
    (unsigned, "sz"), (unsigned, "slot_idx")
  ]

def getLeanFreeSmall : CodegenM Func := do
  importFunction "lean_free_small" (← void) #[((←«void*»), "p")]

def getLeanSmallMemSize : CodegenM Func := do
  importFunction "lean_small_mem_size" (←unsigned) #[((←«void*»), "p")]

def getLeanIncHeartbeat : CodegenM Func := do
  importFunction "lean_inc_heartbeat" (←void) #[]

def getLeanInternalPanic : CodegenM Func := do
  importFunction "lean_internal_panic" (←void) #[((←«const char*»), "msg")]

def getLeanPanicOutOfMemory : CodegenM Func := do
  importFunction "lean_panic_out_of_memory" (←void) #[]

def getLeanPanicUnreachable : CodegenM Func := do
  importFunction "lean_panic_unreachable" (←void) #[]

def getLeanPanicRcOverflow : CodegenM Func := do
  importFunction "lean_panic_rc_overflow" (←void) #[]

def getLeanAlign : CodegenM Func := do
  let size_t ← size_t
  mkFunction "lean_align" size_t #[(size_t, "v"), (size_t, "a")] fun blk params => do
    let v ← getParam! params 0
    let a ← getParam! params 1
    mkReturn blk $ (← v + (← (← (·-· v)) &&& (← a - (1 : UInt64))))

def Constant.LEAN_OBJECT_SIZE_DELTA : CodegenM RValue := do
  getOrCreateConstant "LEAN_OBJECT_SIZE_DELTA" $ 
    getCtx >>= (do ·.newRValueFromUInt64 (← size_t) 8)

def Constant.SIZE_T_SIZE : CodegenM RValue :=
  getOrCreateConstant "SIZE_T_SIZE" do
    let ctx ← getCtx
    let size_t ← size_t
    let sizeTSize ← size_t.getSize
    ctx.newRValueFromUInt64 size_t sizeTSize.toUInt64

def getLeanGetSlotIdx : CodegenM Func := do
  mkFunction "lean_get_slot_idx" (← unsigned) #[((← size_t), "sz")] fun blk params => do
    let sz ← getParam! params 0
    mkReturn blk $ (← (← (← sz / (← Constant.LEAN_OBJECT_SIZE_DELTA)) - (1 : UInt64)) ::: (← unsigned))

-- Assumption: SMALL_ALLOCATOR is always used
def getLeanAllocSmallObject : CodegenM Func := do
  mkFunction "lean_alloc_small_object" (← «lean_object*») #[((← size_t), "sz")] fun blk params => do
    let sz ← getParam! params 0
    let alignedSz ← mkLocalVar blk (← size_t) "alignedSz"
    let alignedSz' ← call (←getLeanAlign) (sz, (← Constant.LEAN_OBJECT_SIZE_DELTA))
    mkAssignment blk alignedSz $ alignedSz'
    let slot ← call (← getLeanGetSlotIdx) alignedSz
    mkReturn blk $ (← (← call (← getLeanAllocSmall) ((← alignedSz ::: (← unsigned)), slot)) ::: (← «lean_object*»))
    
def getLeanAllocCtorMemory : CodegenM Func := do 
  mkFunction "lean_alloc_ctor_memory" (← «lean_object*») #[((← size_t), "sz")] fun blk params => do
    let sz ← getParam! params 0
    let alignedSz ← call (← getLeanAlign) (sz, (← Constant.LEAN_OBJECT_SIZE_DELTA))
    let slot ← call (← getLeanGetSlotIdx) alignedSz
    let memory ← mkLocalVar blk (← «lean_object*») "memory"
    mkAssignment blk memory $
      (←(←call (←getLeanAllocSmall) ((←alignedSz ::: (←unsigned)), slot)) ::: (← «lean_object*»))
    mkIfBranch blk (← alignedSz ·>> sz) 
      (fun then_ => do
        let memory' ← memory ::: (← size_t >>= (·.getPointer))
        let offset ← (← alignedSz / (← Constant.SIZE_T_SIZE)) - (1 : UInt64)
        let access ← mkArrayAccess memory' offset
        mkAssignment then_ access $ (← constantZero (← size_t))
        mkReturn then_ memory
      )
      (fun else_ => mkReturn else_ memory)


def getLeanSmallObjectSize : CodegenM Func := do
  mkFunction "lean_small_object_size" (← unsigned) #[((← «lean_object*»), "o")] fun blk params => do
    let o ← getParam! params 0
    mkReturn blk $ (← call (← getLeanSmallMemSize) (←o ::: (← unsigned)))

def getLeanFreeSmallObject : CodegenM Func := do
  mkFunction "lean_free_small_object" (← void) #[((← «lean_object*»), "o")] fun blk params => do
    let o ← getParam! params 0
    mkReturn blk $ (← call (← getLeanFreeSmall) (←o ::: (← «void*»)))

def getLeanAllocObject : CodegenM Func := do
  importFunction "lean_alloc_object" (← «lean_object*») #[((← size_t), "sz")]

def getLeanFreeObject : CodegenM Func := do
  importFunction "lean_free_object" (← void) #[((← «lean_object*»), "o")]

def getLeanPtrTag : CodegenM Func := do
  mkFunction "lean_ptr_tag" (← uint8_t) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let ty ← getLeanObject
    let res ← (← dereferenceField obj ty 3) ::: (← uint8_t)
    mkReturn blk res

def getLeanPtrOther : CodegenM Func := do
  mkFunction "lean_ptr_other" (← uint8_t) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let ty ← getLeanObject
    let res ← (← dereferenceField obj ty 2) ::: (← uint8_t)
    mkReturn blk res

def getLeanObjectByteSize : CodegenM Func := do
  importFunction "lean_object_byte_size" (← size_t) #[((← «lean_object*»), "o")]

def getLeanIsMT : CodegenM Func := do
  mkFunction "lean_is_mt" (← bool) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let ty ← getLeanObject
    let res ← (← dereferenceField obj ty 0) ::: (← int)
    mkReturn blk $ (← res <<· (0 : UInt64))

def getLeanIsST : CodegenM Func := do
  mkFunction "lean_is_st" (← bool) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let ty ← getLeanObject
    let res ← (← dereferenceField obj ty 0) ::: (← int)
    mkReturn blk $ (← res ·>> (0 : UInt64))

def getLeanIsPersistent : CodegenM Func := do
  mkFunction "lean_is_persistent" (← bool) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let ty ← getLeanObject
    let res ← (← dereferenceField obj ty 0) ::: (← int)
    mkReturn blk $ (← res === (1 : UInt64))

def getLeanIncRefCold : CodegenM Func := do
  importFunction "lean_inc_ref_cold" (←void) #[((← «lean_object*»), "o")]

def getLeanIncRefNCold : CodegenM Func := do
  importFunction "lean_inc_ref_n_cold" (←void) #[((← «lean_object*»), "o"), ((← unsigned), "n")]

def getLeanIncRef : CodegenM Func := do
  mkFunction "lean_inc_ref" (← void)  #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let ty ← getLeanObject
    let isSingleThreaded ← call (← getLeanIsST) obj >>= likely
    mkIfBranch blk isSingleThreaded
      (fun then_ => do
        let m_rc ← dereferenceField obj ty 0
        mkAssignmentOp then_ BinaryOp.Plus m_rc (← constantOne (← int))
        then_.endWithVoidReturn none
      )
      (fun else_ => do
        mkEval else_ $ (← call (← getLeanIncRefCold) obj)
        else_.endWithVoidReturn none
      )

def getLeanIncRefN : CodegenM Func := do
  mkFunction "lean_inc_ref_n" (← void)  #[((← «lean_object*»), "o"), ((← unsigned), "n")] fun blk params => do
    let obj ← getParam! params 0
    let n ← getParam! params 1
    let ty ← getLeanObject
    let isSingleThreaded ← call (← getLeanIsST) obj >>= likely
    mkIfBranch blk isSingleThreaded
      (fun then_ => do
        let m_rc ← dereferenceField obj ty 0
        mkAssignmentOp then_ BinaryOp.Plus m_rc (← n ::: (← int))
        then_.endWithVoidReturn none
      )
      (fun else_ => do
        mkEval else_ $ (← call (← getLeanIncRefNCold) (obj, n))
        else_.endWithVoidReturn none
      )

def getLeanDecRefCold : CodegenM Func := do
  importFunction "lean_dec_ref_cold" (←void) #[((← «lean_object*»), "o")]

def getLeanDecRef : CodegenM Func := do
  mkFunction "lean_dec_ref" (← void)  #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let ty ← getLeanObject
    let m_rc ← dereferenceField obj ty 0
    let isNonExclusive ← (m_rc ·>> (1 : UInt64)) >>= likely
    mkIfBranch blk isNonExclusive
      (fun then_ => do
        mkAssignmentOp then_ BinaryOp.Minus m_rc (← constantOne (← int))
        then_.endWithVoidReturn none
      )
      (fun else_ => do
        mkEval else_ $ (← call (← getLeanDecRefCold) obj)
        else_.endWithVoidReturn none
      )

private def ifNotScalar (name : String)  (onNotScalar : Block → Array LeanGccJit.Core.Param → CodegenM Unit) (extraParam : Array (JitType × String) := #[]) : CodegenM Func := do
  mkFunction name (← void)  (#[((← «lean_object*»), "o")] ++ extraParam) fun blk params => do
    let obj ← getParam! params 0
    let isScalar ← call (← getLeanIsScalar) obj
    mkIfBranch blk isScalar
      (fun then_ => then_.endWithVoidReturn none)
      (fun else_ => do
        onNotScalar else_ params
        else_.endWithVoidReturn none
      )

def getLeanInc : CodegenM Func := 
  ifNotScalar "lean_inc" fun block params => do
    call (← getLeanIncRef) (← getParam! params 0) >>= mkEval block

def getLeanIncN : CodegenM Func := do
  ifNotScalar "lean_inc_n" (fun block params => do
    call (← getLeanIncRefN) ((← getParam! params 0), (← getParam! params 1)) >>= mkEval block)
    #[((← unsigned), "n")]

def getLeanDec : CodegenM Func := 
  ifNotScalar "lean_dec" fun block params => do
    call (← getLeanDecRef) (← getParam! params 0) >>= mkEval block
