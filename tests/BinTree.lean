inductive Tree (A : Type) : Type :=
  | Empty : Tree A
  | Node : Tree A → A -> Tree A -> Tree A

def Tree.insert {A : Type} [Ord A] (x : A) : Tree A → Tree A
  | Empty => Node Empty x Empty
  | Node l y r => match Ord.compare x y with
    | Ordering.lt => Node (Tree.insert x l) y r
    | Ordering.eq => Node l y r
    | Ordering.gt => Node l y (Tree.insert x r)

def Tree.toList {A : Type} : Tree A → List A
  | Empty => []
  | Node l x r => Tree.toList l ++ [x] ++ Tree.toList r

def main (args: List String) : IO Unit := do
  let mut t : Tree Nat := Tree.Empty
  for i in args do
    t := t.insert i.toNat!
  IO.println (t.toList)
