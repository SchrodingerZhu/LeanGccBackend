
structure State (α : Type) :=
  arr : Array α

abbrev TestM := StateM (State Nat)

def push (a : Nat) : TestM Unit := do
  modify (fun s => { s with arr := s.arr.push a })

def run : TestM Unit := do
  for i in [0:50000] do
    push i

def main (_: List String) : IO Unit := do
  let (_, arr) := run { arr := #[] }
  IO.println arr.arr.size
