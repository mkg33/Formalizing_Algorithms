import Mathlib.Tactic

-- # Problem 5

structure SortedArrayFun (n : ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted : Monotone get

open Nat

def contains_bs {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : Option ℕ :=
  bs_aux 0 (n-1) (by omega)
  where bs_aux (a b :ℕ) (h: a ≤ b): Option ℕ  :=
  if h: a = b then
    if q = arr.get a then some a
    else none
  else
    let mid := (a+b)/(2 :ℕ )
    if      q < arr.get mid then bs_aux a mid  (by omega)
    else if  arr.get mid < q then bs_aux (mid+1) b (by omega)
    else some mid



lemma contains_bs_sound_aux {n : ℕ} (arr : SortedArrayFun n) (q : ℕ) :
    ∀ k a b (hle : a ≤ b), b - a ≤ k → ∀ i,
      contains_bs.bs_aux arr q a b hle = some i → arr.get i = q := by
  intro k
  refine Nat.rec (motive := fun k => ∀ a b (hle : a ≤ b), b - a ≤ k → ∀ i,
      contains_bs.bs_aux arr q a b hle = some i → arr.get i = q) ?base ?step k
  · intro a b hle hk i hres
    have hzero : b - a = 0 := Nat.le_zero.mp hk
    have hba : b ≤ a := by
      apply le_of_not_gt
      intro hgt
      have hpos : 0 < b - a := Nat.sub_pos_of_lt hgt
      exact (Nat.ne_of_gt hpos) (by simp [hzero])
    have hEq : a = b := le_antisymm hle hba
    subst hEq
    by_cases h₁ : q = arr.get a
    · simp [contains_bs.bs_aux, h₁] at hres
      rcases hres with rfl
      simp [h₁]
    ·
      simp [contains_bs.bs_aux, h₁] at hres
  · intro k ih a b hle hk i hres
    by_cases hEq : a = b
    · subst hEq
      by_cases h₁ : q = arr.get a
      · simp [contains_bs.bs_aux, h₁] at hres
        rcases hres with rfl
        simp [h₁]
      ·
        simp [contains_bs.bs_aux, h₁] at hres
    · have hltab : a < b := lt_of_le_of_ne hle hEq
      set mid := (a + b) / 2 with hmid
      have hmid_lt_b : mid < b := by
        have htmp : a + b < b + b := Nat.add_lt_add_right hltab b
        have htmp' : a + b < b * 2 := by
          simpa [Nat.mul_two] using htmp
        have : mid < b :=
          (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2 htmp'
        simpa [hmid] using this
      have hleft_le : a ≤ mid := by
        have htmp : a + a ≤ a + b := Nat.add_le_add_left hle a
        have hmul : a * 2 ≤ a + b := by
          simpa [Nat.mul_two] using htmp
        have : a ≤ mid :=
          (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 hmul
        simpa [hmid] using this
      have hright_le : mid + 1 ≤ b := Nat.succ_le_of_lt hmid_lt_b
      unfold contains_bs.bs_aux at hres
      simp [hEq] at hres
      revert hres
      split_ifs with h₁ h₂ <;> intro hres
      · have hk' : mid - a ≤ k := by
          have hlt : mid - a < b - a :=
            Nat.sub_lt_sub_right hleft_le hmid_lt_b
          have hbound : b - a ≤ k.succ := hk
          exact Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hbound)
        exact ih a mid hleft_le hk' i hres
      · have hk' : b - (mid + 1) ≤ k := by
          have a_lt_mid_succ : a < mid + 1 := Nat.lt_succ_of_le hleft_le
          have hlt : b - (mid + 1) < b - a :=
            Nat.sub_lt_sub_left hltab a_lt_mid_succ
          have hbound : b - a ≤ k.succ := hk
          exact Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hbound)
        exact ih (mid + 1) b hright_le hk' i hres
      · have hi : i = mid := by
          simpa [hmid] using (Option.some.inj hres.symm)
        subst hi
        have hle_mid_le_q : arr.get mid ≤ q :=
          le_of_not_gt (by simpa [gt_iff_lt] using h₁)
        have hle_q_le_mid : q ≤ arr.get mid :=
          le_of_not_gt (by simpa [gt_iff_lt] using h₂)
        exact le_antisymm hle_mid_le_q hle_q_le_mid

lemma contains_bs_sound {n : ℕ} (arr : SortedArrayFun n) (q : ℕ) :
    ∀ i, contains_bs arr q = some i → arr.get i = q := by
  intro i hsome
  have hcall :=
    contains_bs_sound_aux arr q (n - 1) 0 (n - 1) (Nat.zero_le _) (by simp) i
      (by simpa [contains_bs])
  exact hcall


theorem Problem5 (n q : ℕ) (_h : 0 < n) (arr : SortedArrayFun n) :
    ∀ i, contains_bs arr q = some i → arr.get i = q :=
  contains_bs_sound arr q
