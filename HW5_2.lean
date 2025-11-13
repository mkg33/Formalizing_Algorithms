import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

-- # Problem 2: Finding Min Sequentially
-- Define minimum property
def Option.MinOfList (result : Option ℕ) (l : List ℕ) : Prop :=
  match result with
  | none => l = []
  | some m => m ∈ l ∧ ∀ x ∈ l, m ≤ x

def List.minHelper (xs : List ℕ)(val_so_far : ℕ) : ℕ := match xs with
  | [] => val_so_far
  | x :: xs => xs.minHelper (min x val_so_far)

def List.FindMin : List ℕ → Option ℕ
  | [] => none
  | x :: xs => some (xs.minHelper x)

-- # In problem 2, prove that FindMIn function correctly compute the mininmum
lemma Problem2 (l : List ℕ) : l.FindMin.MinOfList l := by
  classical
  -- help1: the res of minHelper is: either the acc or an element of the tail
  have mem_or_eq : ∀ (xs : List ℕ) (v : ℕ), (xs.minHelper v = v) ∨ (xs.minHelper v ∈ xs) := by
    intro xs
    induction xs with
    | nil =>
        intro v; simp [List.minHelper]
    | cons x xs ih =>
        intro v
        specialize ih (min x v)
        cases ih with
        | inl h =>
            by_cases hxv : x ≤ v
            · -- min x v = x, so the helper returns x, which is in x :: xs
              right
              have h' : xs.minHelper (min x v) = x := by
                simpa [Nat.min_eq_left hxv] using h
              have : (x :: xs).minHelper v = x := by
                simpa [List.minHelper] using h'
              simp [this, List.mem_cons]
            · -- min x v = v, so the helper returns v
              left
              have hvx : v ≤ x := le_of_lt (lt_of_not_ge hxv)
              have h' : xs.minHelper (min x v) = v := by
                simpa [Nat.min_eq_right hvx] using h
              simp [List.minHelper, h']
        | inr hmem =>
            right
            have : (x :: xs).minHelper v = xs.minHelper (min x v) := by simp [List.minHelper]
            have : xs.minHelper (min x v) ∈ xs := hmem
            simpa [List.minHelper] using List.mem_cons_of_mem x this
  -- help2: minHelper returns a lower bound for every element of (v :: xs)
  have le_all : ∀ (xs : List ℕ) (v y : ℕ), y ∈ v :: xs → xs.minHelper v ≤ y := by
    intro xs
    induction xs with
    | nil =>
        intro v y hy
        -- y must be v in this case
        have : y = v ∨ False := by simpa [List.mem_cons] using hy
        cases this with
        | inl hyv =>
            subst hyv; simp [List.minHelper]
        | inr hfalse => cases hfalse
    | cons x xs ih =>
        intro v y hy
        -- use IH with acc min x v
        have hIH : ∀ z ∈ min x v :: xs, xs.minHelper (min x v) ≤ z := by
          intro z hz; exact ih (min x v) z hz
        have hm_le_min : xs.minHelper (min x v) ≤ min x v := hIH _ (by simp)
        have hm_le_x : xs.minHelper (min x v) ≤ x := le_trans hm_le_min (Nat.min_le_left _ _)
        have hm_le_tail : ∀ z ∈ xs, xs.minHelper (min x v) ≤ z := by
          intro z hz; exact hIH z (by simp [hz])
        have hy_cases : y = v ∨ y = x ∨ y ∈ xs := by
          simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using hy
        cases hy_cases with
        | inl hyv =>
            have : xs.minHelper (min x v) ≤ v := le_trans hm_le_min (Nat.min_le_right _ _)
            simpa [List.minHelper, hyv]
        | inr hy' =>
            cases hy' with
            | inl hyx =>
                simpa [List.minHelper, hyx] using hm_le_x
            | inr hyxs =>
                have : xs.minHelper (min x v) ≤ y := hm_le_tail _ hyxs
                simpa [List.minHelper] using this
  -- finish by splitting on the input list
  cases l with
  | nil => simp [List.FindMin, Option.MinOfList]
  | cons x xs =>
      have hmem : xs.minHelper x ∈ x :: xs := by
        cases mem_or_eq xs x with
        | inl h => simp [List.mem_cons, h]
        | inr h =>
            exact List.mem_cons_of_mem _ h
      have hle : ∀ y ∈ x :: xs, xs.minHelper x ≤ y := by
        intro y hy; exact le_all xs x y hy
      -- the MinOfList facts using hmem and hle
      change xs.minHelper x ∈ x :: xs ∧ ∀ a ∈ x :: xs, xs.minHelper x ≤ a
      exact ⟨hmem, hle⟩
