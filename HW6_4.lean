import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


/- ## Problem 4: Monadic structure on lists
`List` can be viewed as a monad-like `Option`, but allowing multiple possible results. The code below defines `List` as a monad. -/

namespace List

def bind {α β : Type} : List α → (α → List β) → List β
  | [],      _ => []
  | a :: as, f => f a ++ bind as f

def pure {α : Type} (a : α) : List α := [a]

-- Problem 4A: Prove the following.
theorem Problem4A {α β : Type} (a : α) (f : α → List β) :
    bind (pure a) f = f a := by
  simp [bind, pure]

-- Problem 4B: Prove the following
theorem Problem4B {α : Type} :
    ∀as : List α, bind as pure = as := by
  intro as
  induction as with
  | nil =>
      simp [bind]
  | cons a as ih =>
      simp [bind, pure, ih]

-- Helper lemma: bind distributes over append
theorem bind_append {α β : Type} (f : α → List β) :
    ∀xs ys : List α, bind (xs ++ ys) f = bind xs f ++ bind ys f := by
  intro xs ys
  induction xs with
  | nil =>
      simp [bind]
  | cons x xs ih =>
      simp [bind, ih, List.append_assoc]

-- Problem 4C: Prove the following
-- the bind_append theorem may be useful
theorem Problem4C {α β γ : Type} (f : α → List β) (g : β → List γ) :
    ∀as : List α, bind (bind as f) g = bind as (fun a ↦ bind (f a) g) := by
  intro as
  induction as with
  | nil =>
      simp [bind]
  | cons a as ih =>
      -- bind over append, then IH
      have h :=
        bind_append (α := β) (β := γ) (f := g) (xs := f a) (ys := bind as f)
      simpa [bind, ih] using h

end List
