
structure Matrix (M N : Nat) where
  data : { f : FloatArray // f.size = M * N }

def Matrix.get (i : Fin M) (j : Fin N) (A : Matrix M N) : Float :=
  A.data.val.get ⟨ i.val * N + j.val, (
    have a : Nat.succ (i.val * N + j.val) <= i.val * N + N := by apply Nat.add_lt_add_left; exact j.isLt;
    have b : Nat.succ (i.val * N + j.val) <= Nat.succ i.val * N  := by rw [Nat.succ_mul]; exact a;
    have c : Nat.succ i.val <= M := by apply Nat.succ_le_of_lt; exact i.isLt;
    have d : Nat.succ i.val * N <= M * N := by apply Nat.mul_le_mul_right; exact c;
    have e : Nat.succ (i.val * N + j.val) <= M * N := Trans.trans b d;
    by rewrite [A.data.property]; exact e
)⟩

def Matrix.set (i : Fin M) (j : Fin N) (A : Matrix M N) (f : Float) : Matrix M N :=
{data := ⟨A.data.val.set (⟨ i.val * N + j.val, (
    have a : Nat.succ (i.val * N + j.val) <= i.val * N + N := by apply Nat.add_lt_add_left; exact j.isLt;
    have b : Nat.succ (i.val * N + j.val) <= Nat.succ i.val * N  := by rw [Nat.succ_mul]; exact a;
    have c : Nat.succ i.val <= M := by apply Nat.succ_le_of_lt; exact i.isLt;
    have d : Nat.succ i.val * N <= M * N := by apply Nat.mul_le_mul_right; exact c;
    have e : Nat.succ (i.val * N + j.val) <= M * N := Trans.trans b d;
    by rewrite [A.data.property]; exact e
)⟩) f, by simp [FloatArray.set, Array.set, FloatArray.size, Array.size]; exact A.data.property⟩}

def Matrix.zeros (M N : Nat) : Matrix M N :=
  let a := Array.mkArray (M * N) 0.0
  let data := FloatArray.mk a
  { data := ⟨ data, by simp [mkArray, FloatArray.size, Array.size]⟩}

@[specialize]
partial def loop (i : Nat) (j : Nat) (k : Nat) (acc : Matrix M P) (A : Matrix M N) (B : Matrix N P) : Matrix M P :=
  if x : i < M then
    if y : j < P then
      if z : k < N then
        let next := acc.set ⟨i, x⟩ ⟨j, y⟩ (acc.get ⟨i, x⟩ ⟨j, y⟩ + A.get ⟨i, x⟩ ⟨k, z⟩ * B.get ⟨k, z⟩ ⟨j, y⟩)
        loop i j (k+1) next A B
      else
        loop i (j+1) 0 acc A B
    else
      loop (i+1) 0 0 acc A B
  else
    acc

def Matrix.mul (A : Matrix M N) (B : Matrix N P) : Matrix M P :=
  let init := Matrix.zeros M P
  loop 0 0 0 init A B

def main (args : List String) : IO Unit := do
  let args := args.toArray
  if args.size < 2500 then
    panic! "wrong number of arguments"
  else
    let mut A := Matrix.zeros 50 50
    let mut i := 0
    let mut j := 0
    while x : i < 50 do
      while y : j < 50 do
        A := A.set ⟨i, x⟩ ⟨j, y⟩ (args.get! (i * 50 + j)).toNat!.toFloat
        j := j + 1
      j := 0
      i := i + 1
    A := A.mul A
    IO.println A.data.val
