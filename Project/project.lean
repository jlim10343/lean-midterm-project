namespace structural_datatypes

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

infixl:69 " @ " => append

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

theorem mapAppend {α β : Type u} (A : List α) (B : List α) (f : α → β) :
  map f (A @ B) = (map f A) @ (map f B) := by
    induction A with
    | Nil =>
        calc
          map f (List.Nil @ B) = map f B := by rw [append]
          _                    = List.Nil @ (map f B) := by rw [append]
          _                    = (map f List.Nil) @ (map f B) := by rw [map]
    | Cons x xs ih =>
        calc
          map f ((List.Cons x xs) @ B) = map f (List.Cons x (xs @ B)) := by rw [append]
          _                            = List.Cons (f x) (map f (xs @ B)) := by rw [map]
          _                            = List.Cons (f x) ((map f xs) @ (map f B)) := by rw [ih]
          _                            = (List.Cons (f x) (map f xs)) @ (map f B) := by rw [append]
          _                            = (map f (List.Cons x xs)) @ (map f B) := by rw [map]

theorem inordMap {α β : Type u} (T : Tree α) (f : α → β) :
  inord (treeMap f T) = map f (inord T) := by
    induction T with
    | Empty =>
        calc
          inord (treeMap f Tree.Empty) = inord Tree.Empty := by rw [treeMap]
          _                            = List.Nil := by rw [inord]
          _                            = map f List.Nil := by rw [map]
          _                            = map f (inord Tree.Empty) := by rw [inord]
    | Node L x R ihL ihR =>
        calc
          inord (treeMap f (Tree.Node L x R)) = inord (Tree.Node (treeMap f L) (f x) (treeMap f R)) := by rw [treeMap]
          _                                   = (inord (treeMap f L)) @ (List.Cons (f x) (inord (treeMap f R))) := by rw [inord]
          _                                   = (map f (inord L)) @ (List.Cons (f x) (map f (inord R))) := by rw [ihL, ihR]
          _                                   = (map f (inord L)) @ (map f (List.Cons x (inord R))) := by rw [map]
          _                                   = map f ((inord L) @ (List.Cons x (inord R))) := by rw [← mapAppend]
          _                                   = map f (inord (Tree.Node L x R)) := by rw [inord]


end structural_datatypes
