import Mathlib.Tactic -- imports all of the tactics in Lean's maths library


set_option autoImplicit false
set_option tactic.hygienic false


-- We will use the following Monad
structure TimeM (α : Type) where
  ret : α
  time : ℕ

namespace TimeM

def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

-- Increment time

@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

notation "✓" a:arg ", " c:arg => tick a c
notation "✓" a:arg => tick a  -- Default case with only one argument

def tickUnit : TimeM Unit :=
  ✓ () -- This uses the default time increment of 1


-- We define `@[simp]` lemmas for the `.time` field, similar to how we did for `.ret`.
@[grind, simp] theorem time_of_pure {α} (a : α) : (pure a).time = 0 := rfl
@[grind, simp] theorem time_of_bind {α β} (m : TimeM α) (f : α → TimeM β) :
 (TimeM.bind m f).time = m.time + (f m.ret).time := rfl
@[grind, simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl
@[grind, simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- allow us to simplify the chain of compositions
attribute [simp] Bind.bind Pure.pure TimeM.pure

end TimeM

-- ============================================================================
-- Problem 1: Maximum element (20 points)
-- ============================================================================
-- Implement maxT that finds the maximum element in a non-empty list
-- Each comparison should cost 1 time unit
-- Expected time complexity: n-1 comparisons for a list of length n

@[grind] def maxT : List ℕ → TimeM ℕ
| [] => return 0
| [x] => return x
| x :: xs => do
    let r ← maxT xs
    if x ≤ r then
      ✓ r
    else
      ✓ x

@[grind] def mymax : List ℕ → ℕ
| [] => 0
| [x] => x
| x :: xs => max x (mymax xs)

lemma maxT_time_length_sub_one (xs : List ℕ) :
  (maxT xs).time = xs.length - 1 := by
  induction xs with
  | nil => simp [maxT]
  | cons x xs IH =>
      cases xs with
      | nil => simp [maxT]
      | cons y ys =>
          have IH' : (maxT (y :: ys)).time = (y :: ys).length - 1 := by
            simpa using IH
          by_cases h : x ≤ (maxT (y :: ys)).ret
          · simp [maxT, h, IH']
          · simp [maxT, h, IH']

theorem Problem1_maxT_correctness (xs : List ℕ):
  (maxT xs).ret = mymax xs := by
  induction xs with
  | nil => simp [maxT, mymax]
  | cons x xs IH =>
      cases xs with
      | nil => simp [maxT, mymax]
      | cons y ys =>
          have IH' : (maxT (y :: ys)).ret = mymax (y :: ys) := by
            simpa using IH
          by_cases h : x ≤ (maxT (y :: ys)).ret
          ·
            have hx : x ≤ mymax (y :: ys) := by simpa [IH'] using h
            simp [maxT, mymax, IH', hx]
          ·
            have hx_not : ¬x ≤ mymax (y :: ys) := by simpa [IH'] using h
            have hx_lt : mymax (y :: ys) < x := lt_of_not_ge hx_not
            have hx_le : mymax (y :: ys) ≤ x := le_of_lt hx_lt
            simp [maxT, mymax, IH', hx_not, hx_le]

theorem Problem1_maxT_time (xs : List ℕ) (h : xs.length ≥ 1):
  (maxT xs).time = xs.length - 1 := by
  cases xs with
  | nil => cases h
  | cons x xs =>
      simpa using maxT_time_length_sub_one (x :: xs)
