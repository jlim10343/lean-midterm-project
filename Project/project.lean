namespace structural_datatypes

inductive List (α : Type) where
  | Nil : List α
  | Cons : α → List α → List α

def append {α : Type} (l : List α) (r : List α) : List α :=
  match l with
    | List.Nil => r
    | List.Cons x xs => List.Cons x (append xs r)

infixl:69 " @ " => append
infixl:68 " :: " => List.Cons

-- We start off with some simple proofs regarding lists and the "map" function

def map {α β : Type} (f : α → β) (l : List α) : List β :=
  match l with
    | List.Nil => List.Nil
    | List.Cons x xs => (f x)::(map f xs)

theorem mapAppend {α β : Type} (A : List α) (B : List α) (f : α → β) :
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

def len {α : Type} (l : List α) : Nat :=
  match l with
  | List.Nil => 0
  | List.Cons _ xs => 1 + len xs

theorem lenAppend {α : Type} (l1 : List α) (l2 : List α) :
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
def fold {α β : Type} (g : α → β → β) (z : β) (l : List α) : β :=
  match l with
  | List.Nil => z
  | List.Cons x xs => g x (fold g z xs)

theorem foldAppend {α β : Type} (l1 l2 : List α) :
  ∀ g : α → β → β, ∀ z : β, fold g z (l1 @ l2) = fold g (fold g z l2) l1 := by
  intro g z
  induction l1 with
  | Nil =>
      calc
        fold g z (List.Nil @ l2) = fold g z l2 := by rw [append]
        _                        = fold g (fold g z l2) List.Nil := by rw [fold]
  | Cons x xs ih =>
      calc
        fold g z ((x::xs) @ l2) = fold g z (x::(xs @ l2)) := by rw [append]
        _                                = g x (fold g z (xs @ l2)) := by rw [fold]
        _                                = g x (fold g (fold g z l2) xs) := by rw [ih]
        _                                = fold g (fold g z l2) (x::xs) := by rw [fold]

-- Now we can rewrite a lot of the proofs using fold!

def append' {α : Type} (A : List α) (B : List α) : List α :=
  fold (fun x L ↦ x::L) B A

def foldAppendEquiv {α : Type} (A : List α) (B : List α) : append A B = append' A B := by
  induction A with
  | Nil =>
      calc
        append (List.Nil) B = B := by rw [append]
        _                   = fold (fun x (L : List α) ↦ x::L) B List.Nil := by rw [fold]
        _                   = append' List.Nil B := by rw [append']
  | Cons x xs ih =>
      calc
        append (x::xs) B = x::(append xs B) := by rw [append]
        _                = x::(append' xs B) := by rw [ih]
        _                = x::(fold (fun x L ↦ x::L) B xs) := by rw [append']
        _                = (fun x (L : List α) ↦ x::L) x (fold (fun x L ↦ x::L) B xs) := by congr
        _                = fold (fun x (L : List α) ↦ x::L) B (x::xs) := by rw [fold]
        _                = append' (x::xs) B := by rw [append']

-- mapAppend' f B A should be the same as (map f A) @ B
-- The reason why we need an additional append will be apparent when do the later proofs
-- Simply writing map' with just fold will not be enough! We strengthened our hypothesis
def mapAppend' {α β : Type} (f : α → β) (B : List β) : List α →  List β :=
  fold (fun x L ↦ (f x)::L) B

theorem foldMapAppendEquiv {α β : Type} (f : α → β) (B : List β) (A : List α) : (map f A) @ B = mapAppend' f B A := by
  induction A with
  | Nil =>
      calc
        (map f List.Nil) @ B = List.Nil @ B := by rw [map]
        _                    = B := by rw [append]
        _                    = fold (fun x (L : List β) ↦ (f x)::L) B List.Nil := by rw [fold]
        _                    = mapAppend' f B List.Nil := by rw [mapAppend']
  | Cons x xs ih =>
      calc
        (map f (x::xs)) @ B = ((f x)::(map f xs)) @ B := by rw [map]
        _                   = (f x)::((map f xs) @ B) := by rw [append]
        _                   = (f x)::(mapAppend' f B xs) := by rw [ih]
        _                   = (fun x (L : List β) ↦ (f x)::L) x (mapAppend' f B xs) := by congr
        _                   = (fun x (L : List β) ↦ (f x)::L) x (fold (fun x L ↦ (f x)::L) B xs) := by rw [mapAppend']
        _                   = fold (fun x (L : List β) ↦ (f x)::L) B (x::xs) := by rw [fold]
        _                   = mapAppend' f B (x::xs) := by rw [mapAppend']



theorem mapAppend'' {α β : Type} (A : List α) (B : List α) (f : α → β) :
  map f (A @ B) = (map f A) @ (map f B) := by
  have appendNil (l : List β) : l @ List.Nil = l := by
    induction l with
    | Nil => rw [append]
    | Cons x xs ih =>
        calc
          (x::xs) @ List.Nil = x::(xs @ List.Nil) := by rw [append]
          _                  = x::xs := by rw [ih]
  calc
    map f (A @ B) = (map f (A @ B)) @ List.Nil := by rw [appendNil (map f (A @ B))]
    _             = mapAppend' f List.Nil (A @ B) := by rw [foldMapAppendEquiv]
    _             = fold (fun x (L : List β) ↦ (f x)::L) List.Nil (A @ B) := by rw [mapAppend']
    _             = fold (fun x (L : List β) ↦ (f x)::L) (fold (fun x (L : List β) ↦ (f x)::L) List.Nil B) A := by rw [foldAppend]
    _             = fold (fun x (L : List β) ↦ (f x)::L) (mapAppend' f List.Nil B) A := by rw [mapAppend']
    _             = mapAppend' f (mapAppend' f List.Nil B) A := by rw [← mapAppend']
    _             = (map f A) @ (mapAppend' f List.Nil B) := by rw [← foldMapAppendEquiv]
    _             = (map f A) @ ((map f B) @ List.Nil) := by rw [← foldMapAppendEquiv]
    _             = (map f A) @ (map f B) := by rw [appendNil]





-- And here is some fun stuff using trees!

inductive Tree (α : Type) where
  | Empty : Tree α
  | Node : Tree α → α → Tree α → Tree α

def treeMap {α β : Type} (f : α → β) (t : Tree α) : Tree β :=
  match t with
    | Tree.Empty => Tree.Empty
    | Tree.Node L x R => Tree.Node (treeMap f L) (f x) (treeMap f R)

def inord {α : Type} (t : Tree α) : List α :=
  match t with
    | Tree.Empty => List.Nil
    | Tree.Node L x R => (inord L) @ (x::(inord R))

def leaves {α : Type} (t : Tree α) : List α :=
  match t with
    | Tree.Empty => List.Nil
    | Tree.Node L x R =>
        match (L, R) with
        | (Tree.Empty, Tree.Empty) => x::List.Nil
        | _ => (leaves L) @ (leaves R)

def trim {α : Type} (t : Tree α) : Tree α :=
  match t with
  | Tree.Empty => Tree.Empty
  | Tree.Node L x R =>
      match (L, R) with
        | (Tree.Empty, Tree.Empty) => Tree.Empty
        | _ => Tree.Node (trim L) x (trim R)

def size {α : Type} (t : Tree α) : Nat :=
  match t with
  | Tree.Empty => 0
  | Tree.Node L _ R => 1 + size L + size R

theorem inordMap {α β : Type} (T : Tree α) (f : α → β) :
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

theorem trimSize {α : Type} (T : Tree α) :
  size (trim T) + len (leaves T) = size T := by
  induction T with
  | Empty =>
      calc
        size (trim Tree.Empty) + len (leaves Tree.Empty) = size (Tree.Empty) + len (leaves Tree.Empty) := by rw [trim]
        _                              = size (Tree.Empty) + len (List.Nil) := by rw [leaves]
        _                              = 0 + 0 := by rw [size, len]
        _                              = 0 := by rw [Nat.zero_add]
        _                              = size (Tree.Empty) := by rw [size]
  | Node L x R ihL ihR =>
      match (L, R) with
      | (Tree.Empty, Tree.Empty) =>
          calc
            size (trim (Tree.Node Tree.Empty x Tree.Empty)) + len (leaves (Tree.Node Tree.Empty x Tree.Empty)) = size Tree.Empty + len (leaves (Tree.Node Tree.Empty x Tree.Empty)) := by rw [trim]
            _                          = 0 + len (leaves (Tree.Node Tree.Empty x Tree.Empty)) := by rw [size]
            _                          = 0 + len (x::List.Nil) := by rw [leaves]
            _                          = len (x::List.Nil) := by rw [Nat.zero_add]
            _                          = 1 + len List.Nil := by rw [len]
            _                          =

end structural_datatypes
