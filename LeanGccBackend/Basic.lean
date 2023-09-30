
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

import LeanGccJit.Core
open LeanGccJit.Core

namespace Lean.IR
namespace GccJit
def leanMainFn := "_lean_main"

structure GccContext where
  modName    : Name
  jpMap      : JPParamsMap := {}
  mainFn     : FunId := default
  mainParams : Array Param := #[]
  ctx        : Context

structure State where
  rvalueMap   : HashMap VarId RValue
  blockMap    : HashMap JoinPointId Block
  funcMap     : HashMap String Func
  constantMap : HashMap String RValue
  globalMap   : HashMap String LValue
  structMap   : HashMap String (Struct × Array Field)
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

def errorField : CodegenM Field := do
  let ctx ← getCtx
  let void ← ctx.getType TypeEnum.Bool
  ctx.newField none void "_error"

def getBuiltinFunc (name : String) : CodegenM Func :=
  getCtx >>= (·.getBuiltinFunction name)

def likely (x : RValue) : CodegenM RValue := do
  let ctx ← getCtx
  let one ← ctx.one (← ctx.getType TypeEnum.Long)
  let x ← ctx.newCast none x (← ctx.getType TypeEnum.Long)
  let res ← ctx.newCall none (← getBuiltinFunc "__builtin_expect") #[x, one]
  ctx.newCast none res (← ctx.getType TypeEnum.Bool)

def unlikely (x : RValue) : CodegenM RValue := do
  let ctx ← getCtx
  let zero ← ctx.zero (← ctx.getType TypeEnum.Long)
  let x ← ctx.newCast none x (← ctx.getType TypeEnum.Long)
  let res ← ctx.newCall none (← getBuiltinFunc "__builtin_expect") #[x, zero]
  ctx.newCast none res (← ctx.getType TypeEnum.Bool)