
def fib : Nat → Nat
  | Nat.succ m@(Nat.succ n@(Nat.succ _)) => fib m + fib n
  | _ => 1

def main : List String -> IO Unit
  | List.nil => IO.println "empty input"
  | List.cons h _ => IO.println s!"result: {fib h.toNat!}"
