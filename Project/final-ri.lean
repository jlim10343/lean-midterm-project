import Project.midterm

namespace structural_datatypes

inductive Option (α : Type) where
  | NONE : Option α
  | SOME : α → Option α

structure Queue (α : Type) where
  t : Type α

  empty : t
  enq (x : α) (Q : t) : t
  deq (q : t) : Option α

def QueueList : Queue α where
  t := List α

  empty := List.Nil
  enq x Q := x::Q
  deq q :=
    match q with
      | List.Nil => Option.NONE
      | List.Cons x xs => Option.SOME x

def QueueStacks : Queue α where
  t := List α

  empty := List.Nil
  enq x Q := x::Q
  deq q :=
    match q with
      | List.Nil => Option.NONE
      | List.Cons x xs => Option.SOME x

-- Questions to ask patrick
  -- importing mathlib
  -- what should be the type below Bool or Prop??? Equality type????? Tuples?

def isEq {α : Type} (eq : α → α → Bool) : Prop :=
  (∀ a, eq a a) ∧
  (∀ a b, eq a b ↔ eq b a) ∧
  (∀ a b c, (eq a b) ∧ (eq b c) → eq a c)

def queueQuiv {α : Type} (Q : Queue α) (Q' : Queue α) (eq : α → α → Bool) (fxnEq : isEq eq) : Prop :=
  ∃ R : Q.t -> Q'.t -> Prop,
    (R (Q.empty) (Q'.empty)) ∧
    (∀ q q' x, R q q' → R (Q.enq x q) (Q'.enq x q')) ∧
    (∀ q q', R q q' →
      (∃ x, Q.deq q = Option.SOME x → ∃ y, Q'.deq q' = Option.SOME y ∧ eq x y) ∧
      (Q.deq q = Option.NONE → Q'.deq q' = Option.NONE))

theorem stackListRI {α : Type} (eq : α → α → Bool) (fxnEq : isEq eq) : queueQuiv QueueList QueueStacks eq fxnEq :=
  by sorry

end structural_datatypes
