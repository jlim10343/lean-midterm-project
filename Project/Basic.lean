namespace fifteen_one_fifty

inductive List (α : Type u) where
  | Nil : List α
  | Cons : α → List α → List α

inductive Tree (α : Type u) where
  | Empty : Tree α
  | Node : Tree α → α → Tree α → Tree α

end fifteen_one_fifty
