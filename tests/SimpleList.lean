
set_option trace.compiler.ir.result true

def main (x: List String) : IO Unit := do
  let mut arr := [0, 0, 0, 0, 0, 0, 0]
  match x with
  | [a] =>
    for i in [0:a.toNat!] do
      arr := arr.map (· + i)
  | _ => panic! "invalid input"
