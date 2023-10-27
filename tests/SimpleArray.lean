set_option trace.compiler.ir.result true
def main : IO Unit := do
    let mut arr := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    -- for i in [:x] do
    --   arr := arr.map (· + i)
    IO.println arr
