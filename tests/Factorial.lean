def main : List String -> IO Unit
  | List.nil => IO.println "empty input"
  | List.cons h _ => do
    let n := h.toNat!
    IO.println $ n.fold Mul.mul 1
