
def main (x: List String) : IO Unit := do
  let mut sum := 0
  for s in x do
    let n := s.toNat!
    sum := sum + n
  IO.println sum