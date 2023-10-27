import LeanGccBackend.Basic
import LeanGccJit.Core

open LeanGccJit.Core
namespace Lean.IR
namespace GccJit

def LEAN_MAX_SMALL_NAT : Nat := (((1 <<< (System.Platform.numBits - 2)) - 1) <<< 1) + 1

def getLeanObject : CodegenM (Struct × Array Field) := do
  let unsigned ← unsigned
  mkStruct "lean_object" #[
    (← field (← int) "m_rc"),
    (← bitfield unsigned 16 "m_cs_sz"),
    (← bitfield unsigned 8 "m_other"),
    (← bitfield unsigned 8 "m_tag")
  ]
def «lean_object» : CodegenM JitType := do
  getLeanObject >>= (·.fst.asJitType)

def «lean_object*» : CodegenM JitType :=
  getLeanObject >>= (·.fst.asJitType) >>= (·.getPointer)

def getLeanCtorObject : CodegenM (Struct × Array Field) := do
  let obj_ptr ← «lean_object*»
  mkStruct "lean_ctor_object" #[
    (← field obj_ptr "m_header"),
    (← arrayField obj_ptr 0 "m_objs")
  ]

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

def getLeanThunkObject : CodegenM (Struct × Array Field) := do
  let obj_ptr ← «lean_object*»
  let volatile ← obj_ptr.getVolatile
  mkStruct "lean_thunk_object" #[
    (← field (← lean_object) "m_header"),
    (← field volatile "m_value"),
    (← field volatile "m_closure")
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

def getLeanMarkMT : CodegenM Func := do
  importFunction "lean_mark_mt" (←void) #[((← «lean_object*»), "obj")]

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

def getLeanInternalPanicOutOfMemory : CodegenM Func := do
  importFunction "lean_internal_panic_out_of_memory" (←void) #[]

def getLeanInternalPanicUnreachable : CodegenM Func := do
  importFunction "lean_internal_panic_unreachable" (←void) #[]

def getLeanInternalPanicRcOverflow : CodegenM Func := do
  importFunction "lean_internal_panic_rc_overflow" (←void) #[]

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

def Constant.LEAN_CLOSURE_HEADER_SIZE : CodegenM RValue := do
  getOrCreateConstant "LEAN_CLOSURE_HEADER_SIZE" do
    let ctx ← getCtx
    let size_t ← size_t
    let headerSz : UInt64 := 8
    let ptrSz ← Nat.toUInt64 <$> size_t.getSize
    let remSz ← Nat.toUInt64 <$> Mul.mul 2 <$> (← uint16_t).getSize
    ctx.newRValueFromUInt64 size_t (headerSz + ptrSz + remSz)

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
    mkReturn blk $ (← call (← getLeanSmallMemSize) (←o ::: (← «void*»)))

def getLeanFreeSmallObject : CodegenM Func := do
  mkFunction "lean_free_small_object" (← void) #[((← «lean_object*»), "o")] fun blk params => do
    let o ← getParam! params 0
    mkEval blk $ (← call (← getLeanFreeSmall) (←o ::: (← «void*»)))
    blk.endWithVoidReturn none

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
    mkReturn blk $ (← res === (0 : UInt64))

def getLeanHasRc : CodegenM Func := do
  mkFunction "lean_is_persistent" (← bool) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let ty ← getLeanObject
    let res ← (← dereferenceField obj ty 0) ::: (← int)
    mkReturn blk $ (← res =/= (0 : UInt64))

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

def Constant.LeanMaxCtorTag  : UInt64 := 244
def Constant.LeanClosure     : UInt64 := 245
def Constant.LeanArray       : UInt64 := 246
def Constant.LeanStructArray : UInt64 := 247
def Constant.LeanScalarArray : UInt64 := 248
def Constant.LeanString      : UInt64 := 249
def Constant.LeanMPZ         : UInt64 := 250
def Constant.LeanThunk       : UInt64 := 251
def Constant.LeanTask        : UInt64 := 252
def Constant.LeanRef         : UInt64 := 253
def Constant.LeanExternal    : UInt64 := 254
def Constant.LeanReserved    : UInt64 := 255

private def leanIsMux (name : String) (tag_ : UInt64) : CodegenM Func := do
  mkFunction ("lean_is_" ++ name) (← bool) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let tag ← call (← getLeanPtrTag) obj
    mkReturn blk $ (← tag === tag_)

def getLeanIsClosure : CodegenM Func := leanIsMux "closure" Constant.LeanClosure
def getLeanIsArray : CodegenM Func := leanIsMux "array" Constant.LeanArray
def getLeanIsScalarArray : CodegenM Func := leanIsMux "sarray" Constant.LeanScalarArray
def getLeanIsString : CodegenM Func := leanIsMux "string" Constant.LeanString
def getLeanIsMPZ : CodegenM Func := leanIsMux "mpz" Constant.LeanMPZ
def getLeanIsThunk : CodegenM Func := leanIsMux "thunk" Constant.LeanThunk
def getLeanIsTask : CodegenM Func := leanIsMux "task" Constant.LeanTask
def getLeanIsRef : CodegenM Func := leanIsMux "ref" Constant.LeanRef
def getLeanIsExternal : CodegenM Func := leanIsMux "external" Constant.LeanExternal

def getLeanIsCtor : CodegenM Func := do
  mkFunction "lean_is_ctor" (← bool) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let tag ← call (← getLeanPtrTag) obj
    mkReturn blk $ (← tag <== Constant.LeanMaxCtorTag)

def getLeanObjTag : CodegenM Func := do
  let unsigned ← unsigned
  mkFunction "lean_obj_tag" unsigned #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let isScalar ← call (← getLeanIsScalar) obj
    mkIfBranch blk isScalar
      (fun then_ => do
        let tag ← call (← getLeanUnbox) obj
        mkReturn then_ (← tag ::: unsigned)
      )
      (fun else_ => do
        let tag ← call (← getLeanPtrTag) obj
        mkReturn else_ (← tag ::: unsigned)
      )

def getLeanIsExclusive : CodegenM Func := do
  mkFunction "lean_is_exclusive" (← bool) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let isSingleThreaded ← call (← getLeanIsScalar) obj >>= likely
    mkIfBranch blk isSingleThreaded
      (fun then_ => do
        let ty ← getLeanObject
        let m_rc ← dereferenceField obj ty 0
        mkReturn then_ $ (← m_rc === (1 : UInt64))
      )
      (fun else_ => do
        mkReturn else_ (← constantZero (← bool))
      )

def getLeanIsShared : CodegenM Func := do
  mkFunction "lean_is_shared" (← uint8_t) #[((← «lean_object*»), "o")] fun blk params => do
    let obj ← getParam! params 0
    let isSingleThreaded ← call (← getLeanIsScalar) obj >>= likely
    mkIfBranch blk isSingleThreaded
      (fun then_ => do
        let ty ← getLeanObject
        let m_rc ← dereferenceField obj ty 0
        mkReturn then_ $ ← (← m_rc ·>> (1 : UInt64)) ::: (← uint8_t)
      )
      (fun else_ => do
        mkReturn else_ (← constantZero (← uint8_t))
      )

def getLeanInitialize : CodegenM Func := do
  importFunction "lean_initialize" (←void) #[]

def getLeanInitializeRuntimeModule : CodegenM Func := do
  importFunction "lean_initialize_runtime_module" (←void) #[]

def getLeanIOMkWorld : CodegenM Func := do
  mkFunction "lean_io_mk_world" (← «lean_object*») #[] fun blk _ => do
    mkReturn blk $ (←call (← getLeanBox) (← constantZero (← size_t)))

def getLeanIOMarkEndInitialization : CodegenM Func := do
  importFunction "lean_io_mark_end_initialization" (←void) #[]

def getLeanIOResultIsOk : CodegenM Func := do
  mkFunction "lean_io_result_is_ok" (← bool) #[((← «lean_object*»), "r")] fun blk params => do
    let r ← getParam! params 0
    let tag ← call (← getLeanPtrTag) r
    mkReturn blk $ (← tag === (0 : UInt64))

def getLeanInitTaskManager : CodegenM Func := do
  importFunction "lean_init_task_manager" (←void) #[]

def getLeanFinalizeTaskManager : CodegenM Func := do
  importFunction "lean_finalize_task_manager" (←void) #[]

def getLeanIOResultShowError : CodegenM Func := do
  importFunction "lean_io_result_show_error" (←void) #[((← «lean_object*»), "r")]

def getLeanMkString :  CodegenM Func := do
  importFunction "lean_mk_string" (← «lean_object*») #[((← «const char*»), "s")]

def getLeanMkStringFromBytes : CodegenM Func := do
  importFunction "lean_mk_string_from_bytes" (← «lean_object*») #[((← «const char*»), "s"), ((← size_t), "len")]

def getLeanSetSTHeader : CodegenM Func := do
  let unsigned ← unsigned
  mkFunction "lean_set_st_header" (← void)
    #[((← «lean_object*»), "o"), (unsigned, "tag"), (unsigned, "other")] fun blk params => do
    let o ← getParam! params 0
    let object ← getLeanObject
    let tag ← getParam! params 1
    let other ← getParam! params 2
    let m_rc ← dereferenceField o object 0
    let m_cs_sz ← dereferenceField o object 1
    let m_other ← dereferenceField o object 2
    let m_tag ← dereferenceField o object 3
    mkAssignment blk m_rc (← constantOne (← int))
    mkAssignment blk m_cs_sz (← constantZero unsigned)
    mkAssignment blk m_other other
    mkAssignment blk m_tag tag
    blk.endWithVoidReturn none

def getLeanAllocCtor : CodegenM Func := do
  let unsigned ← unsigned
  let size_t ← size_t
  mkFunction "lean_alloc_ctor" (← «lean_object*»)
    #[(unsigned, "tag"), (unsigned, "num_objs"), (unsigned, "scalar_sz")] fun blk params => do
    let tag ← getParam! params 0
    -- TODO: use sizeof once supported
    let leanCtorObjectSize ← Constant.LEAN_OBJECT_SIZE_DELTA
    let ptrSize ← GccJit.size_t >>= (·.getSize) >>= (mkConstant size_t ·.toUInt64)
    let numObjs ← getParam! params 1
    let scalarSz ← getParam! params 2
    let memory ← mkLocalVar blk (← «lean_object*») "memory"
    let size ← (← ptrSize * (← numObjs ::: size_t)) + (← (← leanCtorObjectSize ::: size_t) + (← scalarSz ::: size_t))
    mkAssignment blk memory $ (← call (← getLeanAllocCtorMemory) size)
    mkEval blk $ (← call (← getLeanSetSTHeader) (memory, tag, (← constantZero unsigned)))
    mkReturn blk memory

def getLeanCtorObjCPtr : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  let obj_ptr_ptr ← obj_ptr.getPointer
  mkFunction "lean_ctor_obj_cptr" obj_ptr_ptr #[(obj_ptr, "o")] fun blk params => do
    let o ← getParam! params 0
    let ctorObj ← getLeanCtorObject
    let ctorObjPtr ← ctorObj.fst.asJitType >>= (·.getPointer)
    let casted ← o ::: ctorObjPtr
    let m_objs ← dereferenceField casted ctorObj 1
    mkReturn blk (← arrayToPtr m_objs)

def getLeanCtorSet : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_ctor_set" (← void) #[(obj_ptr, "o"), ((← unsigned), "i"), (obj_ptr, "v")] fun blk params => do
    let o ← getParam! params 0
    let i ← getParam! params 1
    let v ← getParam! params 2
    let ptr ← call (← getLeanCtorObjCPtr) o
    let access ← mkArrayAccess ptr i
    mkAssignment blk access v
    blk.endWithVoidReturn none

def getLeanCtorGet : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_ctor_get" obj_ptr #[(obj_ptr, "o"), ((← unsigned), "i")] fun blk params => do
    let o ← getParam! params 0
    let i ← getParam! params 1
    let ptr ← call (← getLeanCtorObjCPtr) o
    let access ← mkArrayAccess ptr i
    mkReturn blk access

def getLeanApply (arity: Nat) := do
    let objPtr ← «lean_object*»
    let args := (List.range $ arity + 1).map fun i => (objPtr, s!"a{i}")
    importFunction s!"lean_apply_{arity}" (← «lean_object*») (args.toArray)

def getLeanIOResultGetValue : CodegenM Func := do
  --  lean_ctor_get(r, 0)
  mkFunction "lean_io_result_get_value" (← «lean_object*») #[((← «lean_object*»), "r")] fun blk params => do
    mkReturn blk (← call (← getLeanCtorGet) (← getParam! params 0, ← constantZero (← unsigned)))

def getLeanApplyM : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  importFunction "lean_apply_m" obj_ptr #[(obj_ptr, "f"), (← unsigned, "n"), (← obj_ptr.getPointer, "args")]

def getLeanCtorGetAux (name : String) (ty : JitType) : CodegenM Func := do
  let objPtr ← «lean_object*»
  mkFunction s!"lean_ctor_get_{name}" ty #[(objPtr, "o"), (← unsigned, "offset")] fun blk params => do
    let o ← getParam! params 0
    let base ← call (← getLeanCtorObjCPtr) o >>= (bitcast · (← uint8_t >>= (·.getPointer)))
    let tyPtr ← ty.getPointer
    let withOffset ← mkArrayAccess base (← getParam! params 1) >>= (·.getAddress none) >>= (bitcast · tyPtr)
    mkReturn blk (← withOffset.dereference none)

def getLeanCtorGetUsize  : CodegenM Func := do
  let objPtr ← «lean_object*»
  let size_t ← size_t
  mkFunction s!"lean_ctor_get_usize" size_t #[(objPtr, "o"), (← unsigned, "i")] fun blk params => do
    let o ← getParam! params 0
    let base ← call (← getLeanCtorObjCPtr) o >>= (bitcast · (← size_t.getPointer))
    mkReturn blk $ ← mkArrayAccess base (← getParam! params 1)

def getLeanUnboxAux (name : String) (ty : JitType) : CodegenM Func := do
  mkFunction s!"lean_unbox_{name}" ty #[(← «lean_object*», "o")] fun blk params => do
  let o ← getParam! params 0
  if (←ty.getSize) < (← size_t >>= (·.getSize)) && (← ty.isIntegral)
  then do
    let unboxed ← call (← getLeanUnbox) o
    mkReturn blk (← unboxed ::: ty)
  else do
    let func ← getLeanCtorGetAux name ty
    mkReturn blk (← call func (o, (← constantZero (← unsigned))))

def getLeanUnboxUInt32 : CodegenM Func := uint32_t >>= getLeanUnboxAux "uint32"

def getLeanIOResultMkOk : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_io_result_mk_ok" obj_ptr #[(obj_ptr, "a")] fun blk params => do
    let a ← getParam! params 0
    let r ← mkLocalVar blk obj_ptr "r"
    let zero ← constantZero (← unsigned)
    let two ← mkConstant (← unsigned) 2
    let one ← constantOne (← unsigned)
    let unit ← call (← getLeanBox) (← constantZero (← size_t))
    mkAssignment blk r $ (← call (← getLeanAllocCtor) (zero, two, zero))
    mkEval blk $ (← call (← getLeanCtorSet) (r, zero, a))
    mkEval blk $ (← call (← getLeanCtorSet) (r, one, unit))
    mkReturn blk r

def getLeanIOResultIsError : CodegenM Func := do
  mkFunction "lean_io_result_is_error" (← bool) #[((← «lean_object*»), "r")] fun blk params => do
    let r ← getParam! params 0
    let tag ← call (← getLeanPtrTag) r
    mkReturn blk $ (← tag === (1 : UInt64))

def getLeanCtorSetAux (name : String) (ty : JitType) : CodegenM Func := do
  let objPtr ← «lean_object*»
  mkFunction s!"lean_ctor_set_{name}" (← void) #[(objPtr, "o"), (← unsigned, "offset"), (ty, "value")] fun blk params => do
    let o ← getParam! params 0
    let base ← call (← getLeanCtorObjCPtr) o >>= (bitcast · (← uint8_t >>= (·.getPointer)))
    let tyPtr ← ty.getPointer
    let withOffset ← mkArrayAccess base (← getParam! params 1) >>= (·.getAddress none) >>= (bitcast · tyPtr)
    mkAssignment blk (← withOffset.dereference none) (← getParam! params 2)
    blk.endWithVoidReturn none

def getLeanCtorSetUsize : CodegenM Func := do
  let objPtr ← «lean_object*»
  let size_t ← size_t
  mkFunction s!"lean_ctor_set_usize" (← void) #[(objPtr, "o"), (← unsigned, "i"), (size_t, "value")] fun blk params => do
    let o ← getParam! params 0
    let i ← getParam! params 1
    let v ← getParam! params 2
    let base ← call (← getLeanCtorObjCPtr) o >>= (bitcast · (← size_t.getPointer))
    let access ← mkArrayAccess base i
    mkAssignment blk access v
    blk.endWithVoidReturn none

def getLeanBoxAux (name : String) (ty : JitType) : CodegenM Func := do
  let size_t ← size_t
  mkFunction s!"lean_box_{name}" (← «lean_object*») #[(ty, "val")] fun blk params => do
  let val ← getParam! params 0
  let tySize ← ty.getSize
  if tySize < (← size_t.getSize) && (← ty.isIntegral)
  then do
    let val ← val ::: size_t
    mkReturn blk (← call (← getLeanBox) val)
  else do
    let unsigned ← unsigned
    let obj ← mkLocalVar blk (← «lean_object*») "obj"
    let size ← mkConstant unsigned tySize.toUInt64
    mkAssignment blk obj $ (← call (← getLeanAllocCtor) (← constantZero unsigned, ← constantZero unsigned, size))
    let func ← getLeanCtorSetAux name ty
    mkEval blk (← call func (obj, ←constantZero unsigned, val))
    mkReturn blk obj

def getLeanAllocClosure : CodegenM Func := do
  let unsigned ← unsigned
  let obj_ptr ← «lean_object*»
  mkFunction "lean_alloc_closure" obj_ptr #[(← «void*», "fn"), (unsigned, "arity"), (unsigned, "fixed")] fun blk params => do
    let fn ← getParam! params 0
    let arity ← getParam! params 1
    let fixed ← getParam! params 2 >>= (· ::: (← size_t))
    let headerSz ← Constant.LEAN_CLOSURE_HEADER_SIZE
    let ptrSz ← Constant.SIZE_T_SIZE
    let closureSz ← headerSz + (← ptrSz * fixed)
    let alloc ← call (← getLeanAllocSmallObject) closureSz
    let st@(ty, _) ← getLeanClosureObject
    let closurePtr ← ty.asJitType >>= (·.getPointer)
    let closureVar ← mkLocalVar blk closurePtr "closure"
    mkAssignment blk closureVar $ ← alloc ::: closurePtr
    let m_fn ← dereferenceField closureVar st 1
    let m_arity ← dereferenceField closureVar st 2
    let m_fixed ← dereferenceField closureVar st 3
    let uint16_t ← uint16_t
    mkAssignment blk m_fn fn
    mkAssignment blk m_arity $ ← arity ::: uint16_t
    mkAssignment blk m_fixed $ ← fixed ::: uint16_t
    let ptr ← closureVar ::: obj_ptr
    mkEval blk $ ← call (← getLeanSetSTHeader) (ptr, ← mkConstant unsigned Constant.LeanClosure, ← constantZero unsigned)
    mkReturn blk ptr

def getLeanClosureSet : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_closure_set" (← void) #[(obj_ptr, "o"), (← unsigned, "i"), (obj_ptr, "v")] fun blk params => do
    let o ← getParam! params 0
    let i ← getParam! params 1
    let v ← getParam! params 2
    let st@(ty, _) ← getLeanClosureObject
    let closurePtr ← ty.asJitType >>= (·.getPointer)
    let closure ← o ::: closurePtr
    let m_objs ← dereferenceField closure st 4
    let access ← mkArrayAccess m_objs i
    mkAssignment blk access v
    blk.endWithVoidReturn none

def getLeanCtorSetTag : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_ctor_set_tag" (← void) #[(obj_ptr, "o"), (← unsigned, "tag")] fun blk params => do
    let o ← getParam! params 0
    let tag ← getParam! params 1
    let st ← getLeanObject
    let m_tag ← dereferenceField o st 3
    mkAssignment blk m_tag tag
    blk.endWithVoidReturn none

def getLeanCtorRelease : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_ctor_release" (← void) #[(obj_ptr, "o"), (← unsigned, "i")] fun blk params => do
    let o ← getParam! params 0
    let i ← getParam! params 1
    let obj ← mkLocalVar blk (← «lean_object*» >>= (·.getPointer)) "obj"
    let access ← mkArrayAccess (← call (← getLeanCtorObjCPtr) o) i
    mkAssignment blk obj $ ← access.getAddress none
    let obj ← obj.asRValue
    mkEval blk $
      ← call (← getLeanDec) (← obj.dereference none)
    mkAssignment blk (← obj.dereference none) $
      ← call (← getLeanBox) (← constantZero (← size_t))
    blk.endWithVoidReturn none

def getLeanDealloc : CodegenM Func := do
  importFunction "lean_dealloc" (← void) #[((← «lean_object*»), "o")]

def getLeanCStrToNat : CodegenM Func := do
  importFunction "lean_cstr_to_nat" (← «lean_object*») #[((← «const char*»), "s")]

def getLeanBigUSizeToNat : CodegenM Func := do
  importFunction "lean_big_usize_to_nat" (← «lean_object*») #[((← size_t), "o")]

def getLeanBigUInt64ToNat : CodegenM Func := do
  importFunction "lean_big_uint64_to_nat" (← «lean_object*») #[((← uint64_t), "o")]

def getLeanUsizeToNat : CodegenM Func := do
  mkFunction "lean_usize_to_nat" (← «lean_object*») #[((← size_t), "i")] fun blk params => do
    let i ← getParam! params 0
    let isSmall ← (i <== LEAN_MAX_SMALL_NAT.toUInt64) >>= likely
    mkIfBranch blk isSmall
      (fun then_ => do
        mkReturn then_ (← call (← getLeanBox) i)
      )
      (fun else_ => do
        mkReturn else_ (← call (← getLeanBigUSizeToNat) i)
      )

def isBothScalar [AsRValue τ₁] [AsRValue τ₂] (x: τ₁) (y : τ₂) : CodegenM RValue := do
  let size_t ← size_t
  let x ← x ::! size_t
  let y ← y ::! size_t
  (x &&& y) >>= (· &&& (1 : UInt64)) >>= (· =/= (0 : UInt64)) >>= likely

def isBothObject [AsRValue τ₁] [AsRValue τ₂] (x: τ₁) (y : τ₂) : CodegenM RValue := do
  let size_t ← size_t
  let x ← x ::! size_t
  let y ← y ::! size_t
  (x ||| y) >>= (· &&& (1 : UInt64)) >>= (· === (0 : UInt64))

def getLeanUnsignedToNat : CodegenM Func := do
  let unsigned ← unsigned
  mkFunction "lean_unsigned_to_nat" (← «lean_object*») #[((unsigned), "i")] fun blk params => do
    let i ← getParam! params 0
    mkReturn blk $ (← call (← getLeanUsizeToNat) (← i ::: (← size_t)))

def getLeanUInt64ToNat : CodegenM Func := do
  let uint64_t ← uint64_t
  mkFunction "lean_uint64_to_nat" (← «lean_object*») #[((uint64_t), "i")] fun blk params => do
    let i ← getParam! params 0
    let isSmall ← (i <== LEAN_MAX_SMALL_NAT.toUInt64) >>= likely
    mkIfBranch blk isSmall
      (fun then_ => do
        mkReturn then_ (← call (← getLeanBox) i)
      )
      (fun else_ => do
        mkReturn else_ (← call (← getLeanBigUInt64ToNat) i)
      )

def getLeanNatBigBinOp (name : String) (isCompare: Bool := False) : CodegenM Func := do
  let retTy ← if isCompare then uint8_t else «lean_object*»
  importFunction s!"lean_nat_big_{name}" retTy #[((← «lean_object*»), "a"), ((← «lean_object*»), "b")]

def dispatchSignedOverflow (op: String) : CodegenM (Func × JitType) := do
  let ctx ← getCtx
  let size_t ← size_t
  let size_t_size ← size_t.getSize
  let int ← int
  if (← int.getSize) == size_t_size then
    return (← getBuiltinFunc s!"__builtin_s{op}_overflow", int)
  else do
    let long ← ctx.getType TypeEnum.Long
    if (← long.getSize) == size_t_size then
      return (← getBuiltinFunc s!"__builtin_s{op}l_overflow", long)
    else do
      let longlong ← ctx.getType TypeEnum.LongLong
      if (← longlong.getSize) == size_t_size then
        return (← getBuiltinFunc s!"__builtin_s{op}ll_overflow", longlong)
      else
        throw "Unsupported size_t type"

def dispatchOverflowBuiltin (op: String) : CodegenM (Func × JitType) := do
  let ctx ← getCtx
  let size_t ← size_t
  let unsigned ← unsigned
  if ← unsigned.isCompatibleWith size_t then
    return (← getBuiltinFunc s!"__builtin_u{op}_overflow", unsigned)
  else do
    let ulong ← ctx.getType TypeEnum.UnsignedLong
    if ← ulong.isCompatibleWith size_t then
      return (← getBuiltinFunc s!"__builtin_u{op}l_overflow", ulong)
    else do
      let ulonglong ← ctx.getType TypeEnum.UnsignedLongLong
      if ← ulonglong.isCompatibleWith size_t then
        return (← getBuiltinFunc s!"__builtin_u{op}ll_overflow", ulonglong)
      else
        throw "Unsupported size_t type"

def overflowCheck [AsRValue τ₁]  [AsRValue τ₂] (dispatch : String → CodegenM (Func × JitType)) (blk: Block) (name : String) (x : τ₁) (op: String) (y : τ₂) : CodegenM (LValue × RValue) := do
  let (func, ty) ← dispatch op
  let x ← x ::: ty
  let y ← y ::: ty
  let result ← mkLocalVar blk ty name
  let address ← result.getAddress none
  let overflow ← call func (x, y, address)
  pure (result, overflow)

def getLeanNatBinOp
  (name : String)
  (fastpath: Block → LeanGccJit.Core.Param → LeanGccJit.Core.Param → CodegenM Unit)
  (isCompare: Bool := False) : CodegenM Func := do
  let retTy ← if isCompare then uint8_t else «lean_object*»
  mkFunction s!"lean_nat_{name}" retTy #[((← «lean_object*»), "a"), ((← «lean_object*»), "b")] fun blk params => do
    let a ← getParam! params 0
    let b ← getParam! params 1
    let isBothScalar ← isBothScalar a b
    mkIfBranch blk isBothScalar
      (fun then_ => do
        fastpath then_ a b
      )
      (fun else_ => do
        mkReturn else_ (← call (← getLeanNatBigBinOp name isCompare) (a, b))
      )

def getLeanNatAdd : CodegenM Func :=
  getLeanNatBinOp "add" fun blk a b => do
    let size_t ← size_t
    let one ← constantOne size_t
    let a ← a ::! size_t
    let b ← (←b ::! size_t) &&& (← ·~· one)
    let (result, overflow) ← overflowCheck dispatchOverflowBuiltin blk "result" a "add" b
    let overflow ← unlikely overflow
    mkIfBranch blk overflow
      (fun then_ => do
        let topbit ← one <<< (System.Platform.numBits - 1).toUInt64
        let result ← (←result >>> (1 : UInt64)) ||| topbit
        mkReturn then_ $ ← call (← getLeanBigUSizeToNat) (← result ::: size_t)
      )
      (fun else_ => do
        mkReturn else_ $ ← result ::! (←«lean_object*»)
      )

def getLeanNatSub : CodegenM Func :=
  getLeanNatBinOp "sub" fun blk a b => do
    let size_t ← size_t
    let one ← constantOne size_t
    let a ← a ::! size_t
    let b ← (←b ::! size_t) &&& (← ·~· one)
    let (result, overflow) ← overflowCheck dispatchOverflowBuiltin blk "result" a "sub" b
    let overflow ← unlikely overflow
    mkIfBranch blk overflow
      (fun then_ => do
        let unit ← call (← getLeanBox) (← constantZero size_t)
        mkReturn then_ unit
      )
      (fun else_ => do
        mkReturn else_ (← result ::! (←«lean_object*»))
      )

def getLeanNatEq : CodegenM Func := do
  mkFunction "lean_nat_eq" (← uint8_t) #[((← «lean_object*»), "a"), ((← «lean_object*»), "b")] fun blk params => do
    let a ← getParam! params 0
    let b ← getParam! params 1
    mkIfBranch blk (← a === b)
      (fun then_ => do
        mkReturn then_ (← constantOne (← uint8_t))
      )
      (fun else_ => do
        let isBothObject ← isBothObject a b
        mkIfBranch else_ isBothObject
          (fun then_ => do
            mkReturn then_ (← call (← getLeanNatBigBinOp "eq" true) (a, b))
          )
          (fun else_ => do
            mkReturn else_ (← constantZero (← uint8_t))
          )
      )

def getLeanNatLt : CodegenM Func :=
  getLeanNatBinOp "lt" (isCompare := true) fun blk a b => do
    let size_t ← size_t
    let a ← a ::! size_t
    let b ← b ::! size_t
    let cmp ← a <<· b
    mkReturn blk $ ← cmp ::! (← uint8_t)

def getLeanNatLe : CodegenM Func :=
  getLeanNatBinOp "le" (isCompare := true) fun blk a b => do
    let size_t ← size_t
    let a ← a ::! size_t
    let b ← b ::! size_t
    let cmp ← a <== b
    mkReturn blk $ ← cmp ::! (← uint8_t)

def getLeanNatDecLt : CodegenM Func := do
  mkFunction "lean_nat_dec_lt" (← uint8_t) #[((← «lean_object*»), "a"), ((← «lean_object*»), "b")] fun blk params => do
    mkReturn blk $ ← call (← getLeanNatLt) (← getParam! params 0, ← getParam! params 1)

def getLeanNatDecLe : CodegenM Func := do
  mkFunction "lean_nat_dec_le" (← uint8_t) #[((← «lean_object*»), "a"), ((← «lean_object*»), "b")] fun blk params => do
    mkReturn blk $ ← call (← getLeanNatLe) (← getParam! params 0, ← getParam! params 1)

def getLeanNatLAnd : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_nat_land" obj_ptr #[(obj_ptr, "a"), (obj_ptr, "b")] fun blk params => do
    let size_t ← size_t
    let a ← getParam! params 0
    let b ← getParam! params 1
    let a' ← a ::! size_t
    let b' ← b ::! size_t
    let res ← mkLocalVar blk size_t "res"
    mkAssignment blk res $ ← a' &&& b'
    let isScalar ← likely $ ← (← res &&& (1 : UInt64)) =/= (0 : UInt64)
    mkIfBranch blk isScalar
      (fun then_ => do
        mkReturn then_ $ ← res ::! obj_ptr
      )
      (fun else_ => do
        mkReturn else_ $ ← call (← getLeanNatBigBinOp "land") (a, b)
      )

def getLeanNatDecEq : CodegenM Func := do
  mkFunction "lean_nat_dec_eq"  (← uint8_t) #[((← «lean_object*»), "a"), ((← «lean_object*»), "b")] fun blk params => do
    let a ← getParam! params 0
    let b ← getParam! params 1
    mkReturn blk $ ← call (← getLeanNatEq) (a, b)

def getLeanNatDiv : CodegenM Func := do
  getLeanNatBinOp "div" fun blk a b => do
    let a ← call (← getLeanUnbox) a
    let b ← call (← getLeanUnbox) b
    let isZero ← unlikely $ ← b === (0 : UInt64)
    mkIfBranch blk isZero
      (fun then_ => do
        let unit ← call (← getLeanBox) (← constantZero (← size_t))
        mkReturn then_ unit
      )
      (fun else_ => do
        let div ← a / b
        mkReturn else_ $ ← call (← getLeanBox) div
      )

def getLeanNatMod : CodegenM Func := do
  getLeanNatBinOp "mod" fun blk a b => do
    let a' ← call (← getLeanUnbox) a
    let b' ← call (← getLeanUnbox) b
    let isZero ← unlikely $ ← b' === (0 : UInt64)
    mkIfBranch blk isZero
      (fun then_ => do
        mkReturn then_ a
      )
      (fun else_ => do
        let rem ← a' % b'
        mkReturn else_ $ ← call (← getLeanBox) rem
      )

def getLeanNatOverflowMul : CodegenM Func := do
  importFunction "lean_nat_overflow_mul" (← «lean_object*») #[((← size_t), "a"), (← size_t, "b")]

def getLeanNatMul : CodegenM Func := do
  getLeanNatBinOp "mul" fun blk a b => do
    let size_t ← size_t
    let a' ← call (← getLeanUnbox) a
    let isZero ← unlikely $ ← a' === (0 : UInt64)
    mkIfBranch blk isZero
      (fun then_ => do
        mkReturn then_ a
      )
      (fun else_ => do
        let b' ← call (← getLeanUnbox) b
        let (result, overflow) ← overflowCheck dispatchSignedOverflow else_ "result" a' "mul" b'
        let overflow ← unlikely overflow
        mkIfBranch else_ overflow
          (fun then_ => do
            mkReturn then_ $ ← call (← getLeanNatOverflowMul) (a', b')
          )
          (fun else_ => do
            mkReturn else_ $ ← call (← getLeanBox) (← result ::: size_t)
          )
      )

def Constant.__ATOMIC_SEQ_CST : CodegenM RValue := do
  mkConstant (← int) 5

def getLeanThunkGet' : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "__lean_gccjit_thunk_get" obj_ptr #[(obj_ptr, "o")] fun blk params => do
    let o ← getParam! params 0
    let st ← getLeanThunkObject
    let retTy ← «lean_object*»
    let casted ← o ::: (← st.fst.asJitType >>= (·.getPointer))
    let load ← getBuiltinFunc s!"__atomic_load_{(←(←size_t).getSize)}"
    let ptrTy ← load.getParam 0 >>= (·.asRValue) >>= (·.getType)
    let src ← dereferenceField casted st 1 >>= (·.getAddress none)
    let src ← src ::: ptrTy
    let seqCst ← Constant.__ATOMIC_SEQ_CST
    let value ← call load (src, seqCst)
    mkReturn blk $ ← value ::! retTy

def dispatchPlainType (x : String) : CodegenM JitType :=
  match x with
  | "uint8" => uint8_t
  | "uint16" => uint16_t
  | "uint32" => uint32_t
  | "uint64" => uint64_t
  | "usize" => size_t
  | _ => throw "Unsupported type"

def dispatchSafeDiv (x: String) : CodegenM Func := do
  let ty ← dispatchPlainType x
  mkFunction s!"__lean_gccjit_safe_div_{x}" ty #[(ty, "a"), (ty, "b")] fun blk params => do
    let a ← getParam! params 0
    let b ← getParam! params 1
    let isZero ← unlikely $ ← b === (0 : UInt64)
    mkIfBranch blk isZero
      (fun then_ => do
        mkReturn then_ $ ← constantZero ty
      )
      (fun else_ => do
        mkReturn else_ $ ← a / b
      )

def dispatchSafeMod (x: String) : CodegenM Func := do
  let ty ← dispatchPlainType x
  mkFunction s!"__lean_gccjit_safe_mod_{x}" ty #[(ty, "a"), (ty, "b")] fun blk params => do
    let a ← getParam! params 0
    let b ← getParam! params 1
    let isZero ← unlikely $ ← b === (0 : UInt64)
    mkIfBranch blk isZero
      (fun then_ => do
        mkReturn then_ a
      )
      (fun else_ => do
        mkReturn else_ $ ← a % b
      )

def dispatchPlainBinExpr [AsRValue α] [AsRValue β] (ty: String) (x : α) (y : β) (op : String) : CodegenM RValue :=
  match op with
  | "add" => x + y
  | "sub" => x - y
  | "mul" => x * y
  | "div" => do
    call (← dispatchSafeDiv ty) (x, y)
  | "mod" => do
    call (← dispatchSafeMod ty) (x, y)
  | "land" => x &&& y
  | "lor" => x ||| y
  | "xor" => x ^^^ y
  | "shift_left" => do
    let size ← dispatchPlainType ty >>= (·.getSize)
    x <<< (← y % (size * 8).toUInt64)
  | "shift_right" => do
    let size ← dispatchPlainType ty >>= (·.getSize)
    x >>> (← y % (size * 8).toUInt64)
  | _ => throw "Unsupported operation"

def dispatchPlainBinOpFunc (ty: String) (op : String) : CodegenM Func := do
  let t ← dispatchPlainType ty
  mkFunction s!"lean_{ty}_{op}" t #[(t, "a"), (t, "b")] fun blk params => do
    let a ← getParam! params 0
    let b ← getParam! params 1
    mkReturn blk $ ← dispatchPlainBinExpr ty a b op

def dispatchPlainCmpExpr [AsRValue α] [AsRValue β] (x : α) (y : β) (op : String) : CodegenM RValue :=
  match op with
  | "eq" => x === y
  | "lt" => x <<· y
  | "le" => x <== y
  | _ => throw "Unsupported operation"

def dispatchPlainDecCmpFunc (ty: String) (op : String) : CodegenM Func := do
  let t ← dispatchPlainType ty
  let u8 ← uint8_t
  mkFunction s!"lean_{ty}_dec_{op}" u8 #[(t, "a"), (t, "b")] fun blk params => do
    let a ← getParam! params 0
    let b ← getParam! params 1
    mkReturn blk $ ← dispatchPlainCmpExpr a b op >>= (· ::: u8)

def dispatchBuiltinClz (ty : JitType) : CodegenM (Func × JitType) := do
  let ctx ← getCtx
  let size ← ty.getSize
  let uint ← ctx.getType TypeEnum.UnsignedInt
  if size <= (← uint.getSize) then do
    return (← getBuiltinFunc "__builtin_clz", uint)
  else do
    let ulong ← ctx.getType TypeEnum.UnsignedLong
    if size <= (← ulong.getSize) then do
      return (← getBuiltinFunc "__builtin_clzl", ulong)
    else do
      let ulonglong ← ctx.getType TypeEnum.UnsignedLongLong
      if size <= (← ulonglong.getSize) then do
        return (← getBuiltinFunc "__builtin_clzll", ulonglong)
      else
        throw "Unsupported type"

def dispatchLog2 (ty: String) : CodegenM Func := do
  let t ← dispatchPlainType ty
  mkFunction s!"lean_{ty}_log2" t #[(t, "a")] fun blk params => do
    let a ← getParam! params 0
    let (func, intermidiate) ← dispatchBuiltinClz t
    let intermidiateSize ← intermidiate.getSize
    let mask := intermidiateSize.toUInt64 * 8 - 1
    let a ← a ::: intermidiate
    let isZero ← unlikely $ ← a === (0 : UInt64)
    mkIfBranch blk isZero
      (fun then_ => do
        mkReturn then_ $ ← constantZero t
      )
      (fun else_ => do
        let clz ← call func a
        let log2 ← clz ^^^ mask
        mkReturn else_ $ ← log2 ::: t
      )
def dispatchSmallIntegralToNat (ty : String) : CodegenM Func := do
  let t ← dispatchPlainType ty
  let usizeToNat ← getLeanUsizeToNat
  mkFunction s!"lean_{ty}_to_nat" (← «lean_object*») #[(t, "a")] fun blk params => do
    let a ← getParam! params 0
    let a' ← a ::: (← size_t)
    mkReturn blk $ ← call usizeToNat a'

def dispatchOfNat  (ty : String) : CodegenM Unit := do
  let t ← dispatchPlainType ty
  let ofBigNat ← importFunction s!"lean_{ty}_of_big_nat" t #[((← «lean_object*»), "a")]
  let leanIsScalar ← getLeanIsScalar
  let borrowFunc ← mkFunction s!"lean_{ty}_of_nat" t #[(← «lean_object*», "a")] fun blk params => do
    let a ← getParam! params 0
    let isSmall ← call leanIsScalar a >>= likely
    mkIfBranch blk isSmall
      (fun then_ => do
        let unboxed ← call (← getLeanUnbox) a
        mkReturn then_ $ ← unboxed ::: t
      )
      (fun else_ => do
        mkReturn else_ $ ← call ofBigNat a
      )
  discard $  mkFunction s!"lean_{ty}_of_nat_mk" t #[(← «lean_object*», "a")] fun blk params => do
    let a ← getParam! params 0
    let res ← mkLocalVar blk t "res"
    mkAssignment blk res $ ← call borrowFunc a
    mkEval blk $ ← call (← getLeanDec) a
    mkReturn blk res

def registerBuiltinFunc (f : String) : CodegenM Unit := do
  let builtin ← getBuiltinFunc f
  modify fun s => { s with funcMap := s.funcMap.insert f builtin }

def getLeanAllocArray : CodegenM Func := do
  let size_t ← size_t
  let obj_ptr ← «lean_object*»
  mkFunction "lean_alloc_array" obj_ptr #[(size_t, "size"), (size_t, "capacity")] fun blk params => do
    let size ← getParam! params 0
    let capacity ← getParam! params 1
    let ptrSize ← size_t.getSize >>= (pure ·.toUInt64)
    let arrayHeaderSize := 3 * ptrSize
    let allocSize ← (← capacity * ptrSize) + arrayHeaderSize
    let obj ← mkLocalVar blk obj_ptr "obj"
    let arr@(st, _) ← getLeanArrayObject
    let leanArrayObjPtr ← st.asJitType >>= (·.getPointer)
    mkAssignment blk obj $ ← call (← getLeanAllocObject) allocSize
    let obj' ← obj ::: leanArrayObjPtr
    let m_size ← dereferenceField obj' arr 1
    let m_capacity ← dereferenceField obj' arr 2
    mkAssignment blk m_size size
    mkAssignment blk m_capacity capacity
    mkReturn blk obj

def getLeanMkEmptyArrayWithCapacity : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_mk_empty_array_with_capacity" obj_ptr #[⟨ obj_ptr, "capacity" ⟩] fun blk params => do
    let capacity ← getParam! params 0
    let isScalar ← call (← getLeanIsScalar) capacity >>= likely
    mkIfBranch blk isScalar
      (fun then_ => do
        let capacity ← call (← getLeanUnbox) capacity
        let size ← mkConstant (← size_t) 0
        mkReturn then_ $ ← call (← getLeanAllocArray) (size, capacity)
      )
      (fun else_ => do
        let null ← getCtx >>= (·.null obj_ptr)
        mkEval else_ $ ← call (← getLeanInternalPanicOutOfMemory) ()
        mkEval else_ $ ← call (← getBuiltinFunc "__builtin_unreachable") ()
        mkReturn else_ null
      )

def registerBasicFunctions : CodegenM Unit := do
    discard getLeanIsScalar
    discard getLeanBox
    discard getLeanUnbox
    discard getLeanSetExitOnPanic
    discard getLeanSetPanicMessages
    discard getLeanPanicFn
    discard getLeanInternalPanic
    discard getLeanInternalPanicOutOfMemory
    discard getLeanInternalPanicUnreachable
    discard getLeanAlign
    discard getLeanGetSlotIdx
    discard getLeanAllocSmall
    discard getLeanFreeSmall
    discard getLeanSmallMemSize
    discard getLeanIncHeartbeat
    discard getLeanAllocObject
    discard getLeanAllocCtorMemory
    discard getLeanSmallObjectSize
    discard getLeanFreeSmallObject
    discard getLeanAllocObject
    discard getLeanFreeObject
    discard getLeanPtrTag
    discard getLeanPtrOther
    discard getLeanObjectByteSize
    discard getLeanIsMT
    discard getLeanIsST
    discard getLeanIsPersistent
    discard getLeanHasRc
    discard getLeanIncRefCold
    discard getLeanIncRefNCold
    discard getLeanIncRef
    discard getLeanIncRefN
    discard getLeanDecRefCold
    discard getLeanDecRef
    discard getLeanInc
    discard getLeanIncN
    discard getLeanDec
    discard getLeanDealloc
    discard getLeanIsCtor
    discard getLeanIsClosure
    discard getLeanIsArray
    discard getLeanIsScalarArray
    discard getLeanIsString
    discard getLeanIsMPZ
    discard getLeanIsThunk
    discard getLeanIsTask
    discard getLeanIsExternal
    discard getLeanIsRef
    discard getLeanObjTag
    discard getLeanIsExclusive
    discard getLeanIsShared
    discard getLeanMarkMT
    discard getLeanMarkPersistent
    discard getLeanSetSTHeader

def registerCtorFunctions : CodegenM Unit := do
    discard getLeanCtorObjCPtr
    discard getLeanAllocCtor
    discard getLeanCtorGet
    discard getLeanCtorSet
    discard getLeanCtorSetTag
    discard getLeanCtorRelease
    discard getLeanCtorGetUsize
    discard $ getLeanCtorGetAux "uint8" (← uint8_t)
    discard $ getLeanCtorGetAux "uint16" (← uint16_t)
    discard $ getLeanCtorGetAux "uint32" (← uint32_t)
    discard $ getLeanCtorGetAux "uint64" (← uint64_t)
    discard $ getLeanCtorGetAux "float" (← double)
    discard getLeanCtorSetUsize
    discard $ getLeanCtorSetAux "uint8" (← uint8_t)
    discard $ getLeanCtorSetAux "uint16" (← uint16_t)
    discard $ getLeanCtorSetAux "uint32" (← uint32_t)
    discard $ getLeanCtorSetAux "uint64" (← uint64_t)
    discard $ getLeanCtorSetAux "float" (← double)

def registerClosureFunctions : CodegenM Unit := do
    discard getLeanAllocClosure
    discard getLeanClosureSet
    (16 : Nat).forM fun i => do
      discard $ getLeanApply i
    discard getLeanApplyM

def registerNatFunctions : CodegenM Unit := do
    discard getLeanCStrToNat
    discard getLeanBigUSizeToNat
    discard getLeanBigUInt64ToNat
    discard getLeanUsizeToNat
    discard getLeanUnsignedToNat
    discard getLeanUInt64ToNat
    discard $ getLeanNatBigBinOp "add"
    discard $ getLeanNatBigBinOp "sub"
    discard $ getLeanNatBigBinOp "mul"
    discard $ getLeanNatBigBinOp "div"
    discard $ getLeanNatBigBinOp "mod"
    discard $ getLeanNatBigBinOp "land"
    discard $ getLeanNatBigBinOp "eq" true
    discard $ getLeanNatBigBinOp "ne" true
    discard $ getLeanNatBigBinOp "lt" true
    discard $ getLeanNatBigBinOp "le" true
    discard getLeanNatAdd
    discard getLeanNatSub
    discard getLeanNatEq
    discard getLeanNatDecEq
    discard getLeanNatLt
    discard getLeanNatDecLt
    discard getLeanNatLe
    discard getLeanNatDecLe
    discard getLeanNatLAnd
    discard getLeanNatDiv
    discard getLeanNatMod
    discard getLeanNatOverflowMul
    discard getLeanNatMul

def registerUnsignedFunctions : CodegenM Unit := do
    for ty in #["uint8", "uint16", "uint32", "uint64", "usize"] do
      for op in #["add", "sub", "mul", "div", "mod", "land", "lor", "xor", "shift_left", "shift_right"] do
        discard $ dispatchPlainBinOpFunc ty op
      for cmp in #["eq", "lt", "le"] do
        discard $ dispatchPlainDecCmpFunc ty cmp
      discard $ dispatchLog2 ty
      dispatchOfNat ty
      if ty != "uint64" && ty != "usize" then
        discard $ dispatchSmallIntegralToNat ty

def getLeanArraySetPanic : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  importFunction "lean_array_set_panic" obj_ptr #[(obj_ptr, "a"), (obj_ptr, "v")]

def getLeanArrayGetPanic : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  importFunction "lean_array_get_panic" obj_ptr #[(obj_ptr, "def_val")]

def getLeanArraySize : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_array_size" (← size_t) #[(obj_ptr, "a")] fun blk params => do
    let a ← getParam! params 0
    let st@(ty, _) ← getLeanArrayObject
    let a ← a ::: (← ty.asJitType >>= (·.getPointer))
    let size ← dereferenceField a st 1
    mkReturn blk size

def getLeanArrayGetSize : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_array_get_size" obj_ptr #[(obj_ptr, "a")] fun blk params => do
    let a ← getParam! params 0
    let size ← call (← getLeanArraySize) a
    mkReturn blk $ ← call (← getLeanBox) size

def getLeanCopyExpandArray : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  importFunction "lean_copy_expand_array" obj_ptr #[(obj_ptr, "a"), (← bool, "expand")]

def withAssumption [AsRValue τ₁] [AsRValue τ₂] (ret: Option τ₁) (blk: Block) (x : τ₂) (body: Block → CodegenM Unit) : CodegenM Unit := do
  mkIfBranch blk x
    body
    (fun else_ => do
      let unreachable ← getBuiltinFunc "__builtin_unreachable"
      mkEval else_ $ ← call unreachable ()
      match ret with
      | none => else_.endWithVoidReturn none
      | some ret => mkReturn else_ ret
    )

def getLeanEnsureExclusiveArray : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_ensure_exclusive_array" obj_ptr #[(obj_ptr, "a")] fun blk params => do
    let a ← getParam! params 0
    let isExclusive ← call (← getLeanIsExclusive) a >>= likely
    mkIfBranch blk isExclusive
      (fun then_ => do
        mkReturn then_ a
      )
      (fun else_ => do
        let falseValue ← constantZero (← bool)
        let sizeExpr ← call (← getLeanArraySize) a
        let oldSize ← mkLocalVar else_ (← size_t) "old_size"
        mkAssignment else_ oldSize sizeExpr
        mkAssignment else_ a $ ← call (← getLeanCopyExpandArray) (a, falseValue)
        withAssumption (some a) else_ isExclusive fun else_ => do
          withAssumption (some a) else_ (← oldSize === sizeExpr) fun else_ => do
            mkReturn else_ a
      )

def getLeanArrayUSet : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  let size_t ← size_t
  mkFunction "lean_array_uset" obj_ptr #[(obj_ptr, "a"), (size_t, "i"), (obj_ptr, "v")] fun blk params => do
    let a ← getParam! params 0
    let i ← getParam! params 1
    let v ← getParam! params 2
    mkAssignment blk a $ ← call (← getLeanEnsureExclusiveArray) a
    let st@(ty, _) ← getLeanArrayObject
    let a' ← a ::: (← ty.asJitType >>= (·.getPointer))
    let m_data ← dereferenceField a' st 3
    let target ← mkLocalVar blk (←obj_ptr.getPointer) "target"
    mkAssignment blk target $ ← mkArrayAccess m_data i >>= (·.getAddress none)
    mkEval blk $ ← call (← getLeanDec) (←dereference target)
    mkAssignment blk (←dereference target) v
    mkReturn blk a

def getLeanArrayUGet : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  let size_t ← size_t
  mkFunction "lean_array_uget" obj_ptr #[(obj_ptr, "a"), (size_t, "i")] fun blk params => do
    let a ← getParam! params 0
    let i ← getParam! params 1
    let st@(ty, _) ← getLeanArrayObject
    let a' ← a ::: (← ty.asJitType >>= (·.getPointer))
    let m_data ← dereferenceField a' st 3
    let target ← mkLocalVar blk obj_ptr "target"
    mkAssignment blk target $ ← mkArrayAccess m_data i
    mkEval blk $ ← call (← getLeanInc) target
    mkReturn blk target

def getLeanArraySet : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_array_set" obj_ptr #[(obj_ptr, "a"), (obj_ptr, "i"), (obj_ptr, "v")] fun blk params => do
    let a ← getParam! params 0
    let i ← getParam! params 1
    let v ← getParam! params 2
    let func ← blk.getFunction
    let panic ← func.newBlock "panic"
    let checked ← func.newBlock "checked"
    panic.endWithReturn none $ ← call (← getLeanArraySetPanic) (a, v)
    let isScalar ← call (← getLeanIsScalar) i >>= likely
    let ifScalar ← func.newBlock "scalar"
    blk.endWithConditional none isScalar ifScalar panic
    -- Scalar Case
    let idx ← mkLocalVar ifScalar (← size_t) "idx"
    mkAssignment ifScalar idx $ ← call (← getLeanUnbox) i
    let size ← call (← getLeanArraySize) a
    let isOOB ← unlikely $ ← idx >== size
    ifScalar.endWithConditional none isOOB panic checked
    -- Checked Case
    mkReturn checked $ ← call (← getLeanArrayUSet) (a, idx, v)

def getLeanArrayGet : CodegenM Func := do
  let obj_ptr ← «lean_object*»
  mkFunction "lean_array_get" obj_ptr #[(obj_ptr, "def_val"), (obj_ptr, "a"), (obj_ptr, "i")] fun blk params => do
    let def_val ← getParam! params 0
    let a ← getParam! params 1
    let i ← getParam! params 2
    let func ← blk.getFunction
    let panic ← func.newBlock "panic"
    let checked ← func.newBlock "checked"
    panic.endWithReturn none $ ← call (← getLeanArrayGetPanic) def_val
    let isScalar ← call (← getLeanIsScalar) i >>= likely
    let ifScalar ← func.newBlock "scalar"
    blk.endWithConditional none isScalar ifScalar panic
    -- Scalar Case
    let idx ← mkLocalVar ifScalar (← size_t) "idx"
    mkAssignment ifScalar idx $ ← call (← getLeanUnbox) i
    let size ← call (← getLeanArraySize) a
    let isOOB ← unlikely $ ← idx >== size
    ifScalar.endWithConditional none isOOB panic checked
    -- Checked Case
    mkReturn checked $ ← call (← getLeanArrayUGet) (a, idx)

def registerMathKernels: CodegenM Unit := do
    registerBuiltinFunc "cos"
    registerBuiltinFunc "sin"

def registerThunkFunctions : CodegenM Unit := do
    discard getLeanThunkGet'

def regiterArrayFunctions : CodegenM Unit := do
    discard getLeanMkEmptyArrayWithCapacity
    discard getLeanArrayUSet
    discard getLeanArraySet
    discard getLeanArrayUGet
    discard getLeanArrayGet
    discard getLeanArrayGetSize

def populateRuntimeTable : CodegenM Unit := do
    registerBasicFunctions
    registerCtorFunctions
    registerClosureFunctions
    registerNatFunctions
    registerUnsignedFunctions
    registerMathKernels
    registerThunkFunctions
    regiterArrayFunctions
