
structure State (N : Nat) where
  factor : Array Nat
  primes : Array Nat

abbrev Sieve (N : Nat) := StateM (State N)

def getFactor {N : Nat} (i : Nat) : Sieve N Nat := do
  get >>= (pure $ ·.factor.get! i)

def setFactor {N : Nat} (i : Nat) (f : Nat) : Sieve N Unit := do
  modify (fun s => { s with factor := s.factor.set! i f })

def addPrime {N : Nat} (p : Nat) : Sieve N Unit := do
  modify (fun s => { s with primes := s.primes.push p })

def runSieve {N : Nat}  : Sieve N Unit := do
  let mut i : Nat := 2
  while i < N + 1 do
    if (← getFactor i) == 0 then
      setFactor i i
      addPrime i
    for p in (← get >>= (pure ·.primes)) do
      if i * p > N then
        break
      setFactor (i * p) p
      if i % p == 0 then
        break
    i := i + 1

def getPrimes (N : Nat ) : Array Nat :=
  let s : State N := { factor := mkArray (N + 1) 0, primes := #[] }
  let (_, s) := (runSieve.run s).run
  s.primes

def main (xs : List String) : IO Unit := do
  let N := xs.head!.toNat!
  IO.println (getPrimes N).toList
