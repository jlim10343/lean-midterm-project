import Project.midterm

namespace structural_datatypes

inductive Rose (α : Type) where
  | Root : α → List (Rose α) → Rose α

def treePreord {α : Type} (T : Tree α) : List α :=
  match T with
    | Tree.Empty => List.Nil
    | Tree.Node L x R => x::((treePreord L) @ (treePreord R))

def concat {α : Type} (LL : List (List α)) : List α :=
  match LL with
    | List.Nil => List.Nil
    | List.Cons L Ls => L @ concat Ls

def foldl {α β : Type} (g : α → β → β) (z : β) (L : List α) : β :=
  match L with
    | List.Nil => z
    | List.Cons x xs => fold g (g x z) xs

def sizeRose {α : Type} (R : Rose α) : Nat :=
  match R with
    | Rose.Root x rs => 1 + (fold (Nat.add) 0 (map sizeRose rs))

def rosePreord {α : Type} (R : Rose α) : List α :=
  match R with
    | Rose.Root x rs => x::(concat (map rosePreord rs))

end structural_datatypes
