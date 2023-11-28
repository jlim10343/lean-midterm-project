import Project.midterm

namespace structural_datatypes

inductive Rose (α : Type) where
  | Root : α → List (Rose α) → Rose α

def treePreord {α : Type} (T : Tree α) : List α :=
  match T with
    | Tree.Empty => List.Nil
    | Tree.Node L x R => x::((treePreord L) @ (treePreord R))

def foldl {α β : Type} (g : α → β → β) (z : β) (L : List α) : β :=
  match L with
    | List.Nil => z
    | List.Cons x xs => fold g (g x z) xs

-- def sizeRose {α : Type} (R : Rose α) : Nat :=
--   match R with
--     | Rose.Root x rs => 1 + (fold (Nat.add) 0 (map sizeRose rs))

mutual
def rosePreord {α : Type} (R : Rose α) : List α :=
  match R with
    | Rose.Root x rs => x::(mapRosePreord rs)
def mapRosePreord {α : Type} (rs : List (Rose α)) : List α :=
  match rs with
    | List.Nil => List.Nil
    | List.Cons r rs => (rosePreord r) @ (mapRosePreord rs)
end
termination_by
  rosePreord => sizeOf R
  mapRosePreord => sizeOf rs

end structural_datatypes
