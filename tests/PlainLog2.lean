def main : List String → IO Unit
  | [a, b, c, d, e] => do
    let a := a.toNat!.toUInt8.log2
    let b := b.toNat!.toUInt16.log2
    let c := c.toNat!.toUInt32.log2
    let d := d.toNat!.toUInt64.log2
    let e := e.toNat!.toUSize.log2
    println! "a: {a}, b: {b}, c: {c}, d: {d}, e: {e}"
  | _ => throw $ IO.userError "invalid number of arguments"