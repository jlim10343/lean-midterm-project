import Project.midterm

inductive Rose (α : Type u) where
  | Root : α → List (Rose α) → Rose α

def treePreord {α : Type u} (T : Tree α) : List α :=
  match T with
    | Tree.Empty => List.Nil
    | Tree.Node L x R => x::((treePreord L) @ (treePreord R))

def concat {α : Type u} (LL : List (List α)) : List α :=
  match LL with
    | List.Nil => List.Nil
    | List.Cons L Ls => L @ concat Ls

def fold {α β : Type u} (g : α → β → β) (z : β) (L : List α) : β :=
  match L with
    | List.Nil => z
    | List.Cons x xs => fold g (g x z) xs

def sizeRose {α : Type u} (R : Rose α) : Nat :=
  match R with
    | Rose.Root x rs => 1 + (fold (Nat.add) 0 (map sizeRose rs))

def rosePreord {α : Type u} (R : Rose α) : List α :=
  match R with
    | Rose.Root x rs => x::(concat (map rosePreord rs))
