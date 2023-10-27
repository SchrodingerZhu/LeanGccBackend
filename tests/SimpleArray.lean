
set_option trace.compiler.ir.result true

def main (x: List String) : IO Unit := do
  let mut arr := #[0, 1, 0, 1]
  IO.print arr.toList
  IO.print arr
