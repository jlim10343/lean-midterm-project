namespace fifteen_one_fifty

inductive List (α : Type u) where
  | Nil : List α
  | Cons : α → List α → List α

inductive Tree (α : Type u) where
  | Empty : Tree α
  | Node : Tree α → α → Tree α → Tree α

def append {α : Type u} (l : List α) (r : List α) : List α :=
  match l with
    | List.Nil => r
    | List.Cons x xs => List.Cons x (append xs r)

infixl:70 " @ " => append

def map {α β : Type u} (f : α → β) (l : List α) : List β :=
  match l with
    | List.Nil => List.Nil
    | List.Cons x xs => List.Cons (f x) (map f xs)

def treeMap {α β : Type u} (f : α → β) (t : Tree α) : Tree β :=
  match t with
    | Tree.Empty => Tree.Empty
    | Tree.Node L x R => Tree.Node (treeMap f L) (f x) (treeMap f R)

def inord {α : Type u} (t : Tree α) : List α :=
  match t with
    | Tree.Empty => List.Nil
    | Tree.Node L x R => (inord L) @ (List.Cons x (inord R))

end fifteen_one_fifty
