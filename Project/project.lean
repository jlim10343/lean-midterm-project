import Mathlib.Tactic

namespace structural_datatypes

inductive List (α : Type u) where
  | Nil : List α
  | Cons : α → List α → List α

def append {α : Type u} (l : List α) (r : List α) : List α :=
  match l with
    | List.Nil => r
    | List.Cons x xs => List.Cons x (append xs r)

infixl:69 " @ " => append
infixl:68 " :: " => List.Cons

-- We start off with some simple proofs regarding lists and the "map" function

def map {α β : Type u} (f : α → β) (l : List α) : List β :=
  match l with
    | List.Nil => List.Nil
    | List.Cons x xs => (f x)::(map f xs)

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
          map f ((x::xs) @ B) = map f (x::(xs @ B)) := by rw [append]
          _                   = (f x)::(map f (xs @ B)) := by rw [map]
          _                   = (f x)::((map f xs) @ (map f B)) := by rw [ih]
          _                   = ((f x)::(map f xs)) @ (map f B) := by rw [append]
          _                   = (map f (x::xs)) @ (map f B) := by rw [map]

def len {α : Type u} (l : List α) : Nat :=
  match l with
  | List.Nil => 0
  | List.Cons _ xs => 1 + len xs

theorem lenAppend {α : Type u} (l1 : List α) (l2 : List α) :
  len (l1 @ l2) = len l1 + len l2 := by
  induction l1 with
  | Nil =>
      calc
        len (List.Nil @ l2) = len l2 := by rw [append]
        _                   = 0 + len l2 := by rw [Nat.zero_add]
        _                   = len List.Nil + len l2 := by rw [len]
  | Cons x xs ih =>
      calc
        len ((x::xs) @ l2) = len (x::(xs @ l2)) := by rw [append]
        _                  = 1 + len (xs @ l2) := by rw [len]
        _                  = 1 + (len xs + len l2) := by rw [ih]
        _                  = 1 + len xs + len l2 := by rw [Nat.add_assoc]
        _                  = len (x::xs) + len l2 := by rw [len]

-- Notice how all these feel like we're repeating the same proof over again for
-- append. Wouldn't you wish there was one proof that can prove them all?
-- We introduce fold:
def fold {α β : Type u} (g : α → β → β) (z : β) (l : List α) : β :=
  match l with
  | List.Nil => z
  | List.Cons x xs => fold g (g x z) xs

theorem foldAppend {α β : Type u} (l1 l2 : List α) :
  ∀ g : α → β → β, ∀ z : β, fold g z (l1 @ l2) = fold g (fold g z l1) l2 := by
  induction l1 with
  | Nil =>
      intro g z
      calc
        fold g z (List.Nil @ l2) = fold g z l2 := by rw [append]
        _                        = fold g (fold g z List.Nil) l2 := by rw [fold]
  | Cons x xs ih =>
      intro g z
      calc
        fold g z ((List.Cons x xs) @ l2) = fold g z (List.Cons x (xs @ l2)) := by rw [append]
        _                                = fold g (g x z) (xs @ l2) := by rw [fold]
        -- The line below is the reason why we need a different quantification of
        -- the variables for the proof. We want to invoke the IH on (g x z) instead of just z
        _                                = fold g (fold g (g x z) xs) l2 := by rw [ih g (g x z)]
        _                                = fold g (fold g z (List.Cons x xs)) l2 := by rw [fold]

def map' {α β : Type u} (f : α → β) : List α → List β :=
  fold (fun x ↦ fun L ↦ List.Cons (f x) L) List.Nil

theorem foldEquiv : map = map' := by
  ext l






inductive Tree (α : Type u) where
  | Empty : Tree α
  | Node : Tree α → α → Tree α → Tree α

def treeMap {α β : Type u} (f : α → β) (t : Tree α) : Tree β :=
  match t with
    | Tree.Empty => Tree.Empty
    | Tree.Node L x R => Tree.Node (treeMap f L) (f x) (treeMap f R)

def inord {α : Type u} (t : Tree α) : List α :=
  match t with
    | Tree.Empty => List.Nil
    | Tree.Node L x R => (inord L) @ (x::(inord R))

def leaves {α : Type u} (t : Tree α) : List α :=
  match t with
    | Tree.Empty => List.Nil
    | Tree.Node L x R =>
        match (L, R) with
        | (Tree.Empty, Tree.Empty) => x::List.Nil
        | _ => (leaves L) @ (leaves R)

def trim {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | Tree.Empty => Tree.Empty
  | Tree.Node L x R =>
      match (L, R) with
        | (Tree.Empty, Tree.Empty) => Tree.Empty
        | _ => Tree.Node (trim L) x (trim R)

def size {α : Type u} (t : Tree α) : Nat :=
  match t with
  | Tree.Empty => 0
  | Tree.Node L _ R => 1 + size L + size R

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
          _                                   = (inord (treeMap f L)) @ ((f x)::(inord (treeMap f R))) := by rw [inord]
          _                                   = (map f (inord L)) @ ((f x)::(map f (inord R))) := by rw [ihL, ihR]
          _                                   = (map f (inord L)) @ (map f (x::(inord R))) := by rw [map]
          _                                   = map f ((inord L) @ (x::(inord R))) := by rw [← mapAppend]
          _                                   = map f (inord (Tree.Node L x R)) := by rw [inord]

theorem trimSize {α : Type u} (T : Tree α) :
  size (trim T) + len (leaves T) = size T := by
  induction T with
  | Empty =>
      calc
        size (trim Tree.Empty) + len (leaves Tree.Empty) = size (Tree.Empty) + len (leaves Tree.Empty) := by rw [trim]
        _                              = size (Tree.Empty) + len (List.Nil) := by rw [leaves]
        _                              = 0 + 0 := by rw [size, len]
        _                              = 0 := by sorry
        _                              = size (Tree.Empty) := by rw [size]
  | Node L x R ihL ihR => sorry

end structural_datatypes
