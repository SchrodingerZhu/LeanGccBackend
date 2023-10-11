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
partial def fib' (n : Nat) (b00 b01 b10 b11 : Nat) (a00 a01 a10 a11 : Nat)  : Nat :=  
  if n == 0
  then b00 + b10
  else 
    let s00 := a00 * a00 + a01 * a10
    let s01 := a00 * a01 + a01 * a11
    let s10 := a10 * a00 + a11 * a10
    let s11 := a10 * a01 + a11 * a11
    if n &&& 1 == 0
    then 
      fib' (n / 2) b00 b01 b10 b11 s00 s01 s10 s11 
    else
      let b00 := b00 * a00 + b01 * a10
      let b01 := b00 * a01 + b01 * a11
      let b10 := b10 * a00 + b11 * a10
      let b11 := b10 * a01 + b11 * a11
      fib' (n / 2) b00 b01 b10 b11 s00 s01 s10 s11

def fib (n : Nat) : Nat :=
  fib' (n - 1) 1 0 0 1 0 1 1 1

def main : List String -> IO Unit
  | List.nil => IO.println \"empty input\"
  | List.cons h _ => IO.println s!\"result: {fib h.toNat!}\"
"

partial def fib' (n : Nat) (b00 b01 b10 b11 : Nat) (a00 a01 a10 a11 : Nat)  : Nat :=  
  if n == 0
  then a00 + a10
  else 
    let s00 := a00 * a00 + a01 * a10
    let s01 := a00 * a01 + a01 * a11
    let s10 := a10 * a00 + a11 * a10
    let s11 := a10 * a01 + a11 * a11
    if n &&& 1 == 0
    then 
      fib' (n >>> 1) b00 b01 b10 b11 s00 s01 s10 s11 
    else
      let b00 := b00 * a00 + b01 * a10
      let b01 := b00 * a01 + b01 * a11
      let b10 := b10 * a00 + b11 * a10
      let b11 := b10 * a01 + b11 * a11
      fib' (n >>> 1) b00 b01 b10 b11 s00 s01 s10 s11


def main : IO Unit := do 
  Lean.initSearchPath  (← Lean.findSysroot)
  let (env, x) ← Lean.Elab.runFrontend src {} "test.lean" `Main
  GccJit.emitGccJit env `Main "/tmp/test.o"
