import «LeanGccBackend»
import «LeanGccBackend».Basic
import «LeanGccBackend».Runtime
import «LeanGccBackend».Codegen
import «LeanGccJit»
import Lean.Util.Path
import Lean.Elab.Frontend
open Lean.IR
open LeanGccJit.Core
open Lean.Elab.Frontend

def src := "
def fib:  Nat -> Nat
  | Nat.succ m@(Nat.succ n) => fib n + fib m
  | _ => 1
def main : List String -> IO Unit
  | List.nil => IO.println \"empty input\"
  | List.cons h _ => IO.println s!\"result: {fib h.toNat!}\"
"

def main : IO Unit := do 
  Lean.initSearchPath  (← Lean.findSysroot)
  let (env, x) ← Lean.Elab.runFrontend src {} "test.lean" `Main
  GccJit.emitGccJit env `Main "/tmp/test.o"
