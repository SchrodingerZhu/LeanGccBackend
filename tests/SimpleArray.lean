def main (_: List String) : IO Unit := do
  let mut arr := #[0, 1, 0, 1]
  for i in arr.toList do
    IO.print i
