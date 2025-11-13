import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

-- For Problem 2, we work on the binary search algorithm for bitonic sorted array

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


-- # Problem 2: Prove that the following binary search algorithm returns index of maximum value in an bitonic array.
def find_idx_peak {n : ℕ}(arr : BitonicSortedArrayFun n) : ℕ :=
     aux 0 (n-1)
  where
    aux (a b : ℕ) (h : a ≤ b := by omega) : ℕ :=
      if h_eq : a = b then a
      else
        let mid := (a+b) / (2 :ℕ)
        if arr.get mid < arr.get (mid + 1) then
          -- We are on the increasing slope, so the peak is in the right half.
          aux (mid + 1) b
        else
          -- We are on the decreasing slope (or mid is the peak).
          -- The peak is in the left half, including mid.
          aux a mid

def IsPeakInRange {n :ℕ }(arr : BitonicSortedArrayFun n) (a b: ℕ): Prop :=
  arr.peak_idx ∈ Set.Icc a b

-- task1:
-- Formulate and prove the following intermediate statement statement in Lean:
-- The index of the peak is in the range [a,b] if and only if the algorithm find_idx_peak.aux is correct on [a,b].

def AuxCorrectOnRange {n : ℕ} (arr : BitonicSortedArrayFun n) (a b : ℕ) : Prop :=
  if h_eq : a = b then
    by
      subst h_eq
      exact IsPeakInRange arr a a
  else
    let mid := (a + b) / 2
    if arr.get mid < arr.get (mid + 1) then
      IsPeakInRange arr (mid + 1) b
    else
      IsPeakInRange arr a mid

lemma iff_lt_peak {n : ℕ} (arr : BitonicSortedArrayFun n) (i : ℕ) :
    arr.get i < arr.get (i + 1) ↔ i < arr.peak_idx := by
  classical
  obtain ⟨_, hmono, hanti⟩ := arr.peak_idx_spec
  constructor
  · intro hlt
    by_contra hnot
    have hk : arr.peak_idx ≤ i := le_of_not_gt hnot
    have hi : i ∈ Set.Ici arr.peak_idx := hk
    have hi1 : i + 1 ∈ Set.Ici arr.peak_idx := by
      exact le_trans hk (Nat.le_succ i)
    have dec : arr.get (i + 1) < arr.get i := hanti hi hi1 (Nat.lt_succ_self i)
    exact (lt_irrefl _) (lt_trans hlt dec)
  · intro hlt
    have hi : i ∈ Set.Icc 0 arr.peak_idx := ⟨Nat.zero_le _, le_of_lt hlt⟩
    have hi1 : i + 1 ∈ Set.Icc 0 arr.peak_idx := ⟨Nat.zero_le _, Nat.succ_le_of_lt hlt⟩
    exact hmono hi hi1 (Nat.lt_succ_self i)

theorem Task1_find_idx_peak_aux_correct_iff {n : ℕ}
  (arr : BitonicSortedArrayFun n) (a b : ℕ) (h : a ≤ b) :
  IsPeakInRange arr a b ↔ AuxCorrectOnRange arr a b := by
  classical
  by_cases hEq : a = b
  · subst hEq
    simp [IsPeakInRange, AuxCorrectOnRange]
  ·
    let mid := (a + b) / 2
    have h_two_pos : 0 < 2 := by decide
    have h_a_le_mid : a ≤ mid := by
      have hmul₂ : 2 * a ≤ a + b := by
        simpa [two_mul, Nat.add_comm] using Nat.add_le_add_left h a
      have hmul : a * 2 ≤ a + b := by
        simpa [Nat.mul_comm] using hmul₂
      have : a ≤ (a + b) / 2 := (Nat.le_div_iff_mul_le h_two_pos).2 hmul
      simpa [mid] using this
    have h_mid_le_b : mid ≤ b := by
      have hmul₂ : a + b ≤ 2 * b := by
        simpa [two_mul] using Nat.add_le_add_right h b
      have : (a + b) / 2 ≤ b := Nat.div_le_of_le_mul hmul₂
      simpa [mid] using this
    constructor
    · intro hk
      rcases hk with ⟨ha, hb⟩
      by_cases hmk : mid < arr.peak_idx
      ·
        have hcond : arr.get mid < arr.get (mid + 1) := (iff_lt_peak arr mid).2 hmk
        have hx : IsPeakInRange arr (mid + 1) b := ⟨Nat.succ_le_of_lt hmk, hb⟩
        simpa [AuxCorrectOnRange, hEq, mid, hcond] using hx
      ·
        have hcond : ¬ arr.get mid < arr.get (mid + 1) := by
          simpa [iff_lt_peak arr mid] using hmk
        have hx : IsPeakInRange arr a mid := ⟨ha, le_of_not_gt hmk⟩
        simpa [AuxCorrectOnRange, hEq, mid, hcond] using hx
    · intro hstep
      by_cases hcond : arr.get mid < arr.get (mid + 1)
      ·
        have hx : IsPeakInRange arr (mid + 1) b := by
          simpa [AuxCorrectOnRange, hEq, mid, hcond] using hstep
        rcases hx with ⟨hL, hR⟩
        have ha : a ≤ arr.peak_idx :=
          le_trans (le_trans h_a_le_mid (Nat.le_succ _)) hL
        exact ⟨ha, hR⟩
      ·
        have hx : IsPeakInRange arr a mid := by
          simpa [AuxCorrectOnRange, hEq, mid, hcond] using hstep
        rcases hx with ⟨hL, hR⟩
        have hb : arr.peak_idx ≤ b := le_trans hR h_mid_le_b
        exact ⟨hL, hb⟩

-- task2: State the theorem and prove it
-- [theorem Problem2A_find_peak_correct_range]
theorem Problem2A_find_peak_correct_range {n : ℕ}
  (arr : BitonicSortedArrayFun n) (a b : ℕ) (h : a ≤ b) :
  IsPeakInRange arr a b ↔ AuxCorrectOnRange arr a b :=
  Task1_find_idx_peak_aux_correct_iff arr a b h


-- L1
lemma lt_to_lt_sub_add_one {k n : ℕ} (hk : k < n) (hn : 1 ≤ n) :
  k < n - 1 + 1 := by
  simpa [Nat.sub_add_cancel hn] using hk


-- L2
lemma add_lt_mul_two_of_lt {a b : ℕ} (h : a < b) :
  a + b < b * 2 := by
  simpa [mul_two] using add_lt_add_right h b

-- L3
lemma left_le_mid_of_le {a b : ℕ} (h : a ≤ b) :
  a ≤ (a + b) / 2 := by
  -- 2a ≤ a + b
  have h₂ : a * 2 ≤ a + b := by
    simpa [mul_two] using Nat.add_le_add_left h a
  -- a ≤ (a + b) / 2  ↔  a*2 ≤ a + b  since 0 < 2
  have hpos : 0 < 2 := Nat.succ_pos 1
  exact (Nat.le_div_iff_mul_le hpos).2 h₂

-- L4
lemma mid_le_right_of_le {a b : ℕ} (h : a ≤ b) :
  (a + b) / 2 ≤ b := by
  have : a + b ≤ 2 * b := by
    simpa [two_mul] using Nat.add_le_add_right h b
  exact Nat.div_le_of_le_mul this

-- L5
lemma peak_eq_of_in_singleton {n : ℕ} (arr : BitonicSortedArrayFun n) {a : ℕ}
  (h : IsPeakInRange arr a a) : arr.peak_idx = a := by
  rcases h with ⟨ha, hb⟩
  exact le_antisymm hb ha

-- L6
lemma lt_succ_iff_le {a b : ℕ} : a < b + 1 ↔ a ≤ b :=
  Nat.lt_succ_iff

lemma le_of_lt_succ {a b : ℕ} (h : a < b + 1) : a ≤ b :=
  (lt_succ_iff_le).1 h

lemma lt_succ_of_le {a b : ℕ} (h : a ≤ b) : a < b + 1 :=
  (lt_succ_iff_le).2 h


-- L7
lemma peak_in_full_range {n : ℕ} (h : 0 < n) (arr : BitonicSortedArrayFun n) :
  IsPeakInRange arr 0 (n - 1) := by
  have hk : arr.peak_idx < n :=
    (BitonicSortedArrayFun.peak_idx_spec arr).1
  have h0 : 0 ≤ arr.peak_idx := Nat.zero_le _
  have hsucc : (n - 1) + 1 = n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt h)
  have hle : arr.peak_idx ≤ n - 1 := by
    have : arr.peak_idx < (n - 1) + 1 := by
      simpa [hsucc] using hk
    exact (Nat.lt_succ_iff.mp this)
  exact And.intro h0 hle

-- L8
lemma peak_in_full_range_init {n : ℕ}
  (arr : BitonicSortedArrayFun n) (hn : 0 < n) :
  IsPeakInRange arr 0 (n - 1) := by
  have hk : arr.peak_idx < n := (arr.peak_idx_spec).1
  exact ⟨Nat.zero_le _, Nat.le_pred_of_lt hk⟩


-- L9
lemma peak_in_singleton_iff_eq {n : ℕ} (arr : BitonicSortedArrayFun n) (a : ℕ) :
  IsPeakInRange arr a a ↔ arr.peak_idx = a := by
  -- IsPeakInRange arr a a  ≡  a ≤ peak ≤ a  ≡  peak = a
  unfold IsPeakInRange
  constructor
  · intro h
    rcases h with ⟨ha, hb⟩
    exact le_antisymm hb ha
  · intro h
    subst h
    exact ⟨le_rfl, le_rfl⟩

-- L10
lemma peak_in_left_of_peak_le_mid {n : ℕ} (arr : BitonicSortedArrayFun n)
    {lo hi mid : ℕ} :
    IsPeakInRange arr lo hi → arr.peak_idx ≤ mid → IsPeakInRange arr lo mid := by
  intro h hle
  rcases h with ⟨hlo, _hhi⟩
  exact ⟨hlo, hle⟩

lemma peak_in_right_of_mid_lt_peak {n : ℕ} (arr : BitonicSortedArrayFun n)
    {lo hi mid : ℕ} :
    IsPeakInRange arr lo hi → mid < arr.peak_idx → IsPeakInRange arr (mid + 1) hi := by
  intro h hlt
  rcases h with ⟨_hlo, hhi⟩
  exact ⟨Nat.succ_le_of_lt hlt, hhi⟩


-- L11
lemma shr_right_m
  {a b mid : ℕ} (h_lt : a < mid + 1) (h_le : mid + 1 ≤ b) :
  b - (mid + 1) < b - a := by
  have h_lt_b : a < b := lt_of_lt_of_le h_lt h_le
  exact Nat.sub_lt_sub_left h_lt_b h_lt

-- L12
lemma aux_correct_on_full_range {n : ℕ}
  (arr : BitonicSortedArrayFun n) (hn : 0 < n) :
  AuxCorrectOnRange arr 0 (n - 1) := by
  have hI : IsPeakInRange arr 0 (n - 1) := peak_in_full_range_init arr hn
  have hle : 0 ≤ n - 1 := Nat.zero_le _
  exact (Problem2A_find_peak_correct_range arr 0 (n - 1) hle).1 hI

-- L13
lemma mid_lt_right_of_lt {a b : ℕ} (h : a < b) :
  (a + b) / 2 < b := by
  have hmul : a + b < 2 * b := by
    simpa [Nat.mul_comm] using add_lt_mul_two_of_lt h
  exact Nat.div_lt_of_lt_mul hmul

-- L14
lemma shr_left_m
  {a b mid : ℕ} (h_le : a ≤ mid) (h_lt : mid < b) :
  mid - a < b - a :=
  Nat.sub_lt_sub_right h_le h_lt

-- L15
lemma aux_eq_peak_of_aux_correct {n : ℕ} (arr : BitonicSortedArrayFun n) :
  ∀ {a b : ℕ} (hle : a ≤ b),
    AuxCorrectOnRange arr a b →
    find_idx_peak.aux arr a b hle = arr.peak_idx := by
  classical
  have main :
      ∀ w : ℕ,
        ∀ {a b : ℕ} (hle : a ≤ b),
          b - a ≤ w →
          AuxCorrectOnRange arr a b →
          find_idx_peak.aux arr a b hle = arr.peak_idx :=
    by
      refine Nat.rec ?base ?step
      · intro a b hle hwidth hAux
        have hzero : b - a = 0 := Nat.le_zero.mp hwidth
        have hba : b ≤ a := Nat.sub_eq_zero_iff_le.mp hzero
        have hEq : a = b := Nat.le_antisymm hle hba
        subst hEq
        have hsingleton : IsPeakInRange arr a a := by
          simpa [AuxCorrectOnRange] using hAux
        have hpeak : arr.peak_idx = a :=
          (peak_in_singleton_iff_eq arr a).1 hsingleton
        simpa [find_idx_peak.aux, hpeak.symm]
      · intro w IH a b hle hwidth hAux
        by_cases hEq : a = b
        · subst hEq
          have hsingleton : IsPeakInRange arr a a := by
            simpa [AuxCorrectOnRange] using hAux
          have hpeak : arr.peak_idx = a :=
            (peak_in_singleton_iff_eq arr a).1 hsingleton
          simpa [find_idx_peak.aux, hpeak.symm]
        ·
          have hlt : a < b := lt_of_le_of_ne hle hEq
          let mid := (a + b) / 2
          have h_left : a ≤ mid := left_le_mid_of_le hle
          have h_mid_lt : mid < b := mid_lt_right_of_lt hlt
          have h_mid_succ_le : mid + 1 ≤ b := Nat.succ_le_of_lt h_mid_lt
          have h_a_lt_mid_succ : a < mid + 1 := lt_succ_of_le h_left
          by_cases hSlope : arr.get mid < arr.get (mid + 1)
          ·
            have hRange : IsPeakInRange arr (mid + 1) b := by
              simpa [AuxCorrectOnRange, hEq, mid, hSlope] using hAux
            have hAuxRight :
                AuxCorrectOnRange arr (mid + 1) b :=
              (Problem2A_find_peak_correct_range arr (mid + 1) b h_mid_succ_le).1 hRange
            have hDropLt :
                b - (mid + 1) < b - a := by
              simpa using shr_right_m h_a_lt_mid_succ h_mid_succ_le
            have hDropLe :
                b - (mid + 1) ≤ w := by
              have hLess := lt_of_lt_of_le hDropLt hwidth
              exact (lt_succ_iff_le).1 hLess
            have hRec :
                find_idx_peak.aux arr (mid + 1) b h_mid_succ_le = arr.peak_idx :=
              IH h_mid_succ_le hDropLe hAuxRight
            simpa [find_idx_peak.aux, hEq, mid, hSlope, hRec]
          ·
            have hRange : IsPeakInRange arr a mid := by
              simpa [AuxCorrectOnRange, hEq, mid, hSlope] using hAux
            have hAuxLeft :
                AuxCorrectOnRange arr a mid :=
              (Problem2A_find_peak_correct_range arr a mid h_left).1 hRange
            have hDropLt :
                mid - a < b - a := by
              simpa using shr_left_m h_left h_mid_lt
            have hDropLe :
                mid - a ≤ w := by
              have hLess := lt_of_lt_of_le hDropLt hwidth
              exact (lt_succ_iff_le).1 hLess
            have hRec :
                find_idx_peak.aux arr a mid h_left = arr.peak_idx :=
              IH h_left hDropLe hAuxLeft
            simpa [find_idx_peak.aux, hEq, mid, hSlope, hRec]
  intro a b hle hAux
  have hbound : b - a ≤ b - a := le_rfl
  exact main (b - a) hle hbound hAux

-- task3: Use the formulation in the previous step to prove the correctness of this algorithm.
theorem Problem2B_find_peak_correct {n : ℕ} (h : 0 < n)
    (arr : BitonicSortedArrayFun n) :
    find_idx_peak arr = arr.peak_idx := by
  classical
  have hAux :
      AuxCorrectOnRange arr 0 (n - 1) :=
    aux_correct_on_full_range (arr := arr) h
  have hle : 0 ≤ n - 1 := Nat.zero_le _
  simpa [find_idx_peak] using
    aux_eq_peak_of_aux_correct (arr := arr) (a := 0) (b := n - 1) hle hAux
