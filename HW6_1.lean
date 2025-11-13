import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

-- For Problem 1 and 2, we work on the binary search algorithm for bitonic sorted array

def Bitonic (f : ℕ → ℤ) (n : ℕ) : Prop :=
  ∃ k,  k < n ∧
    StrictMonoOn f (Set.Icc 0 k) ∧   -- nondecreasing on [0,k]
    StrictAntiOn f (Set.Ici k)       -- nonincreasing on [k, ∞)

-- A "bitonic" array is an array that strictly increases and then strictly decreases, like [1, 4, 8, 10, 5, 2]. The goal is to find the "peak" element (10). The search logic is:
-- Look at mid and mid+1.
-- If arr.get mid < arr.get (mid+1), the peak must be in the right half.
-- If arr.get mid > arr.get (mid+1), the peak is in the left half (and mid could be it).

def IsMaximum (f : ℕ → ℤ) (n : ℕ) (k : ℕ) : Prop :=
  k < n ∧ ∀ i < n, f i ≤ f k

structure BitonicSortedArrayFun (n :ℕ) where
  get : ℕ → ℤ
  size : ℕ := n
  bitonic: Bitonic get n

-- This property appears in the analysis, marking noncomoputable is fine.
noncomputable
def BitonicSortedArrayFun.peak_idx {n :ℕ} (arr: BitonicSortedArrayFun n) := (arr.bitonic).choose
lemma BitonicSortedArrayFun.peak_idx_spec {n :ℕ} (arr: BitonicSortedArrayFun n) : arr.peak_idx < n ∧
  StrictMonoOn arr.get (Set.Icc 0 arr.peak_idx) ∧ StrictAntiOn arr.get (Set.Ici arr.peak_idx) := (arr.bitonic).choose_spec

-- # Problem 1: prove that BitonicSortedArrayFun has a unique maximum which is arr.peak_idx
theorem Problem1 {n : ℕ} (arr : BitonicSortedArrayFun n) :
  IsMaximum arr.get n arr.peak_idx ∧ ∀ (y : ℕ), IsMaximum arr.get n y → y = arr.peak_idx := by
  classical
  have hk_lt_n : arr.peak_idx < n := (arr.peak_idx_spec).1
  have hmono : StrictMonoOn arr.get (Set.Icc 0 arr.peak_idx) := (arr.peak_idx_spec).2.1
  have hanti : StrictAntiOn arr.get (Set.Ici arr.peak_idx) := (arr.peak_idx_spec).2.2
  -- show it's max
  have hmax : IsMaximum arr.get n arr.peak_idx := by
    refine ⟨hk_lt_n, ?_⟩
    intro i hi_lt_n
    cases le_total i arr.peak_idx with
    | inl hi_le_k =>
        cases lt_or_eq_of_le hi_le_k with
        | inl hi_lt_k =>
            have hi_mem : i ∈ Set.Icc 0 arr.peak_idx := ⟨Nat.zero_le _, le_of_lt hi_lt_k⟩
            have hk_mem : arr.peak_idx ∈ Set.Icc 0 arr.peak_idx := ⟨Nat.zero_le _, le_rfl⟩
            have : arr.get i < arr.get arr.peak_idx := hmono hi_mem hk_mem hi_lt_k
            exact le_of_lt this
        | inr h_eq =>
            simp [h_eq]
    | inr hk_le_i =>
        cases lt_or_eq_of_le hk_le_i with
        | inl hk_lt_i =>
            have hk_mem' : arr.peak_idx ∈ Set.Ici arr.peak_idx := by
              show arr.peak_idx ≤ arr.peak_idx
              exact le_rfl
            have hi_mem' : i ∈ Set.Ici arr.peak_idx := hk_le_i
            have hlt : arr.get i < arr.get arr.peak_idx := hanti hk_mem' hi_mem' hk_lt_i
            exact le_of_lt hlt
        | inr h_eq =>
            simp [h_eq]
  -- unique
  refine ⟨hmax, ?_⟩
  intro y hy
  -- comparison
  cases le_total y arr.peak_idx with
  | inl hy_le_k =>
      cases lt_or_eq_of_le hy_le_k with
      | inl hy_lt_k =>
          have hk_le_y : arr.get arr.peak_idx ≤ arr.get y := hy.2 _ hk_lt_n
          have hy_mem : y ∈ Set.Icc 0 arr.peak_idx := ⟨Nat.zero_le _, le_of_lt hy_lt_k⟩
          have hk_mem : arr.peak_idx ∈ Set.Icc 0 arr.peak_idx := ⟨Nat.zero_le _, le_rfl⟩
          have hlt : arr.get y < arr.get arr.peak_idx := hmono hy_mem hk_mem hy_lt_k
          exact False.elim ((lt_irrefl (arr.get arr.peak_idx)) (lt_of_le_of_lt hk_le_y hlt))
      | inr hy_eq =>
          simp [hy_eq]
  | inr hk_le_y =>
      cases lt_or_eq_of_le hk_le_y with
      | inl hk_lt_y =>
          have hk_le_y' : arr.get arr.peak_idx ≤ arr.get y := hy.2 _ hk_lt_n
          have hk_mem' : arr.peak_idx ∈ Set.Ici arr.peak_idx := by
            show arr.peak_idx ≤ arr.peak_idx
            exact le_rfl
          have hy_mem' : y ∈ Set.Ici arr.peak_idx := hk_le_y
          have hlt' : arr.get y < arr.get arr.peak_idx := hanti hk_mem' hy_mem' hk_lt_y
          exact False.elim ((lt_irrefl (arr.get arr.peak_idx)) (lt_of_le_of_lt hk_le_y' hlt'))
      | inr hk_eq_y =>
          simp [hk_eq_y.symm]
