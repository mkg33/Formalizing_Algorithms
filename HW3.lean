import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- All tactics are welcome.

-- # Problem 1
-- Prove that the list reverse operation does not change the length of the list.
def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs


lemma len_append {α} : ∀ xs ys : List α, len (xs ++ ys) = len xs + len ys := by
  intro xs
  induction' xs with a xs ih <;> intro ys
  · simp [len]
  · simp [len, ih, Nat.add_assoc]

lemma len_reverse_aux {α} : ∀ xs : List α, len (reverse xs) = len xs := by
  intro xs
  induction' xs with a xs ih
  · simp [reverse, len]
  · simp [reverse, len, len_append, ih, Nat.add_comm]


theorem problem1 (xs : List ℕ) : len xs = len (reverse xs) := by
  simpa using (len_reverse_aux (α := ℕ) xs).symm


-- # Problem 2: Consider the following recursive function
def S : ℕ → ℕ  → ℕ
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 0
  | n+1, k =>
    if n + 1 = k then 1
    else k * (S n k) + (S n (k-1))

#check Nat.twoStepInduction


lemma S_succ_one : ∀ n, S (n+1) 1 = 1 := by
  refine Nat.rec ?base ?step
  · simp [S]
  · intro n ih
    have hzero : S (n.succ) 0 = 0 := by simp [S]
    have hneq : n.succ + 1 ≠ 1 := by
      simp
    have hstep : S (n.succ.succ) 1 = 1 * S (n.succ) 1 + S (n.succ) 0 := by
      have :
          S (n.succ.succ) 1 =
            if n.succ + 1 = 1 then 1 else 1 * S (n.succ) 1 + S (n.succ) (1 - 1) := rfl
      simpa [if_neg hneq] using this
    calc
      S (n.succ.succ) 1 = S (n.succ) 1 := by simpa [hzero] using hstep
      _ = 1 := by simpa using ih


theorem problem2 (n : ℕ) (h : 0 < n) : S n 1 = 1 := by
  cases' n with m
  · cases h
  · simpa using S_succ_one m


-- # Problem 3
-- This is a continuation of Problem 2
-- You may want to use the result from theorem problem2 to prove problem3
theorem problem3 (n : ℕ) : S n 2 = 2^(n-1) - 1 := by
  induction' n with n ih
  · -- n = 0
    simp [S]
  · -- n = n.succ
    by_cases hdiag : n.succ = 2
    · -- diagonal (n = 1)
      have hn : n = 1 := by
        have : Nat.succ n = Nat.succ 1 := by simpa using hdiag
        exact Nat.succ.inj this
      simp [S, hn]
    · -- off-diagonal
      have hrec : S (n.succ) 2 = 2 * S n 2 + S n 1 := by
        have : S (n.succ) 2 = if n.succ = 2 then 1 else 2 * S n 2 + S n 1 := rfl
        have hneg : (if n.succ = 2 then 1 else 2 * S n 2 + S n 1)
            = 2 * S n 2 + S n 1 := if_neg hdiag
        exact this.trans hneg
      cases' n with m
      · -- the small edge: n = 0
        simp [S]
      · -- now n = m.succ ≥ 1, so S n 1 = 1
        have Sn1 : S (m.succ) 1 = 1 := problem2 _ (Nat.succ_pos _)
        have step1 :
            S (m.succ.succ) 2 + 1 = 2 * S (m.succ) 2 + 2 := by
          -- unfold
          calc
            S (m.succ.succ) 2 + 1
                = (2 * S (m.succ) 2 + S (m.succ) 1) + 1 := by simp [hrec]
            _ = 2 * S (m.succ) 2 + (S (m.succ) 1 + 1) := by ac_rfl
            _ = 2 * S (m.succ) 2 + 2 := by simp [Sn1]
        have step :
            S (m.succ.succ) 2 + 1 = 2 * (S (m.succ) 2 + 1) := by
          simpa [Nat.mul_add, add_comm] using step1
        -- use IH: S (m.succ) 2 = 2^m - 1
        have ih' : S (m.succ) 2 = 2^m - 1 := by simpa [Nat.succ_sub_one] using ih
        -- 2^m ≥ 1 for all m
        have hpos : 1 ≤ 2^m := by
          simpa using (Nat.one_le_pow m 2 (by decide : 0 < 2))
        -- substitute
        have : S (m.succ.succ) 2 + 1 = 2 * 2^m := by
          simpa [ih', Nat.sub_add_cancel hpos] using step
        -- 2 * 2^m = 2^(m+1)
        have : S (m.succ.succ) 2 + 1 = 2^(m+1) := by
          simpa [Nat.pow_succ, Nat.mul_comm] using this
        -- subtract 1 
        have : S (m.succ.succ) 2 = 2^(m+1) - 1 := by
          simpa using congrArg (fun t => t - 1) this
        -- rewrite 
        simpa [Nat.succ_sub_one] using this


-- # Problem 4
def R (r s : ℕ) : ℕ :=
  if r = 0 ∨ s = 0 then 0
  else if r ≤ 1 ∨ s ≤ 1 then 1
  else if r = 2 ∨ s = 2 then 2
  else R (r - 1) s + R r (s - 1)

lemma succ_succ_ne_one (n : ℕ) : Nat.succ (Nat.succ n) ≠ (1 : ℕ) := by
  intro h
  have h' := congrArg Nat.pred h
  change Nat.succ n = 0 at h'
  exact Nat.succ_ne_zero _ h'

private lemma eq_zero_or_one_of_le_one {n : ℕ} (h : n ≤ 1) : n = 0 ∨ n = 1 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
      cases n with
      | zero => exact Or.inr rfl
      | succ n =>
          have : 2 ≤ Nat.succ (Nat.succ n) := by
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          have : Nat.succ 1 ≤ 1 := le_trans this h
          exact (Nat.not_succ_le_self 1 this).elim

-- You may find this useful
#check Nat.choose_eq_choose_pred_add

-- Hint
lemma problem4 (r s : ℕ) : R r s ≤ (r + s - 2).choose (r - 1) := by
  classical
  have main :
      ∀ n : ℕ, ∀ {r s : ℕ}, r + s = n →
        R r s ≤ (r + s - 2).choose (r - 1) :=
    fun n =>
      Nat.strongRecOn
        (motive := fun n => ∀ {r s}, r + s = n → R r s ≤ (r + s - 2).choose (r - 1)) n
        (fun n IH {r s} hsum =>
          by
            by_cases h0 : r = 0 ∨ s = 0
            · have hR : R r s = 0 := by simp [R, h0]
              exact hR ▸ Nat.zero_le _
            · have hr_ne_zero : r ≠ 0 := by
                intro hr
                exact h0 (Or.inl hr)
              have hs_ne_zero : s ≠ 0 := by
                intro hs
                exact h0 (Or.inr hs)
              have hr_pos : 0 < r := Nat.pos_of_ne_zero hr_ne_zero
              have hs_pos : 0 < s := Nat.pos_of_ne_zero hs_ne_zero
              by_cases h1 : r ≤ 1 ∨ s ≤ 1
              · rcases h1 with hrle | hsle
                · rcases eq_zero_or_one_of_le_one hrle with hr0 | hr1
                  · exact (hr_ne_zero hr0).elim
                  · subst hr1
                    have hs0 : s ≠ 0 := hs_ne_zero
                    have : R 1 s = (1 + s - 2).choose (1 - 1) := by
                      simp [R, hs0]
                    exact this.le
                · rcases eq_zero_or_one_of_le_one hsle with hs0 | hs1
                  · exact (hs_ne_zero hs0).elim
                  · subst hs1
                    have hr0 : r ≠ 0 := hr_ne_zero
                    have : R r 1 = (r + 1 - 2).choose (r - 1) := by
                      have : r + 1 - 2 = r - 1 := by simp
                      simp [R, hr0, this, Nat.choose_self]
                    exact this.le
              · obtain ⟨hr_not_le1, hs_not_le1⟩ := not_or.mp h1
                have hr_gt1 : 1 < r := lt_of_not_ge hr_not_le1
                have hs_gt1 : 1 < s := lt_of_not_ge hs_not_le1
                by_cases h2 : r = 2 ∨ s = 2
                · rcases h2 with hr2 | hs2
                  · subst hr2
                    have hsnotle : ¬ s ≤ 1 := not_le.mpr hs_gt1
                    have hs0 : s ≠ 0 := by
                      intro hs
                      exact h0 (Or.inr hs)
                    have hR : R 2 s = 2 := by
                      simp [R, hs0, hsnotle]
                    have hs_ge2 : 2 ≤ s := Nat.succ_le_of_lt hs_gt1
                    have : (2 + s - 2).choose (2 - 1) = s := by
                      simp
                    have : R 2 s ≤ (2 + s - 2).choose (2 - 1) := by
                      simpa [hR, this] using hs_ge2
                    simpa using this
                  · subst hs2
                    have hrnotle : ¬ r ≤ 1 := not_le.mpr hr_gt1
                    have hr0 : r ≠ 0 := by
                      intro hr
                      exact h0 (Or.inl hr)
                    have hR : R r 2 = 2 := by
                      simp [R, hr0, hrnotle]
                    have hr_ge2 : 2 ≤ r := Nat.succ_le_of_lt hr_gt1
                    have hchoose : r.choose (r - 1) = r := by
                      cases' r with r
                      · exact (hr0 rfl).elim
                      · simp [Nat.choose_succ_self_right]
                    have hcoerce : (r + 2 - 2).choose (r - 1) = r.choose (r - 1) := by
                      simp
                    have : 2 ≤ (r + 2 - 2).choose (r - 1) := by
                      have : 2 ≤ r.choose (r - 1) := by
                        simpa [hchoose] using hr_ge2
                      simpa [hcoerce] using this
                    simpa [hR] using this
                · have hle : ¬ (r ≤ 1 ∨ s ≤ 1) := not_or.mpr ⟨hr_not_le1, hs_not_le1⟩
                  have htwo : ¬ (r = 2 ∨ s = 2) := h2
                  have lt1 : (r - 1) + s < n := by
                    have hlt : r - 1 < r := Nat.pred_lt (Nat.ne_of_gt hr_pos)
                    have : (r - 1) + s < r + s := Nat.add_lt_add_right hlt s
                    simpa [hsum] using this
                  have lt2 : r + (s - 1) < n := by
                    have hlt : s - 1 < s := Nat.pred_lt (Nat.ne_of_gt hs_pos)
                    have : r + (s - 1) < r + s := Nat.add_lt_add_left hlt r
                    simpa [hsum] using this
                  have ih1 :
                      R (r - 1) s ≤ ((r - 1) + s - 2).choose (r - 2) :=
                    (IH ((r - 1) + s) lt1) rfl
                  have ih2 :
                      R r (s - 1) ≤ (r + (s - 1) - 2).choose (r - 1) :=
                    (IH (r + (s - 1)) lt2) rfl
                  have hsum1 : (r - 1) + s - 2 = n - 3 := by
                    have : (r - 1) + s = n - 1 := by
                      have hr1 : 1 ≤ r := Nat.succ_le_of_lt hr_pos
                      have : r + s - 1 = (r - 1) + s := by
                        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                          using Nat.add_sub_assoc hr1 s
                      simpa [hsum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm
                    simpa [Nat.sub_sub] using congrArg (fun t => t - 2) this
                  have hsum2 : r + (s - 1) - 2 = n - 3 := by
                    have : r + (s - 1) = n - 1 := by
                      have hs1 : 1 ≤ s := Nat.succ_le_of_lt hs_pos
                      have : r + s - 1 = r + (s - 1) := by
                        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                          using Nat.add_sub_assoc hs1 r
                      simpa [hsum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm
                    simpa [Nat.sub_sub] using congrArg (fun t => t - 2) this
                  have ih1' : R (r - 1) s ≤ (n - 3).choose (r - 2) := by
                    simpa [hsum1] using ih1
                  have ih2' : R r (s - 1) ≤ (n - 3).choose (r - 1) := by
                    simpa [hsum2] using ih2
                  have hr_ge2 : 2 ≤ r := Nat.succ_le_of_lt hr_gt1
                  have hs_ge2 : 2 ≤ s := Nat.succ_le_of_lt hs_gt1
                  have hr_ne2 : r ≠ 2 := by intro hr2; exact htwo (Or.inl hr2)
                  have hs_ne2 : s ≠ 2 := by intro hs2; exact htwo (Or.inr hs2)
                  have hr_gt2 : 2 < r := lt_of_le_of_ne hr_ge2 (by symm; exact hr_ne2)
                  have hs_gt2 : 2 < s := lt_of_le_of_ne hs_ge2 (by symm; exact hs_ne2)
                  have R_split : R r s = R (r - 1) s + R r (s - 1) := by
                    classical
                    set A := R (r - 1) s
                    set B := R r (s - 1)
                    unfold R
                    -- final
                    simp [h0, hle, htwo, A, B]
                  have sum_le_aux := Nat.add_le_add ih1' ih2'
                  have hsum_ge4 : 4 ≤ r + s := Nat.add_le_add hr_ge2 hs_ge2
                  have hn2 : 0 < n - 2 := by
                    have : 2 < r + s := lt_of_lt_of_le (by decide : 2 < 4) hsum_ge4
                    simpa [hsum] using Nat.sub_pos_of_lt this
                  have hk : 0 < r - 1 := Nat.sub_pos_of_lt hr_gt1
                  have pascal :
                      (n - 3).choose (r - 2) + (n - 3).choose (r - 1)
                        = (n - 2).choose (r - 1) := by
                    have :=
                      Nat.choose_eq_choose_pred_add (n := n - 2) (k := r - 1) hn2 hk
                    simpa [Nat.sub_sub, Nat.add_comm] using this.symm
                  have sum_final :
                      R (r - 1) s + R r (s - 1) ≤ (n - 2).choose (r - 1) :=
                    by simpa [pascal] using sum_le_aux
                  have final : R r s ≤ (n - 2).choose (r - 1) :=
                    R_split.symm ▸ sum_final
                  simpa [hsum] using final)
  have : R r s ≤ (r + s - 2).choose (r - 1) := main (r + s) (r := r) (s := s) rfl
  simpa using this

private lemma choose_le_two_pow (n k : ℕ) : (n.choose k) ≤ 2 ^ n := by
  induction' n with n ih generalizing k
  · cases k <;> simp
  · cases k with
    | zero =>
        have : 1 ≤ 2 ^ (n + 1) :=
          Nat.one_le_pow (n + 1) 2 (by decide : 0 < 2)
        simpa [Nat.pow_succ] using this
    | succ k =>
        have hrec := Nat.choose_succ_succ n k
        have h₁ : n.choose k ≤ 2 ^ n := ih _
        have h₂ : n.choose (k.succ) ≤ 2 ^ n := ih _
        have hsum : n.choose k + n.choose (k + 1) ≤ 2 ^ n + 2 ^ n :=
          Nat.add_le_add h₁ h₂
        have hsum' : n.choose k + n.choose (k + 1) ≤ 2 ^ n * 2 := by
          simpa [two_mul, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
            using hsum
        simpa [hrec, Nat.pow_succ, Nat.mul_comm] using hsum'

lemma problem4_exponential (r s : ℕ) : R r s ≤ 2 ^ (r + s) := by
  have h₁ := problem4 r s
  have h₂ : (r + s - 2).choose (r - 1) ≤ 2 ^ (r + s - 2) := by
    simpa using choose_le_two_pow (r + s - 2) (r - 1)
  have h₃ : 2 ^ (r + s - 2) ≤ 2 ^ (r + s) := by
    have hbase : 0 < (2 : ℕ) := by decide
    have hle : r + s - 2 ≤ r + s := Nat.sub_le _ _
    exact Nat.pow_le_pow_right hbase hle
  exact (le_trans h₁ (le_trans h₂ h₃))


-- # Problem 5.1

def interleave : List ℕ → List ℕ → List ℕ
| [], ys => ys
| xs, [] => xs
| x :: xs, y :: ys => x :: y :: interleave xs ys

/--
 * interleave [1, 2, 3] [4, 5, 6] should produce [1, 4, 2, 5, 3, 6].
 * interleave [1, 2] [3, 4, 5, 6] should produce [1, 3, 2, 4, 5, 6].
 * interleave [1, 2, 3, 4] [5, 6] should produce [1, 5, 2, 6, 3, 4].
 * interleave [] [1, 2] should produce [1, 2].
 * interleave [1, 2] [] should produce [1, 2].
 --/

-- length
lemma len_interleave (xs ys : List ℕ) :
  len (interleave xs ys) = len xs + len ys := by
  revert ys
  induction' xs with x xs ih <;> intro ys
  · simp [interleave, len]
  · cases' ys with y ys
    · simp [interleave, len]
    · simp [interleave, len, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

-- # Problem 5.2
-- Recall len and reverse functions from Problem 5.1
theorem problem5_part2 (xs ys : List ℕ) :
  len (reverse (interleave xs ys)) = len (reverse xs) + len ys := by
  have hL := len_reverse_aux (interleave xs ys)
  have hR := len_reverse_aux xs
  simp [hL, hR, len_interleave xs ys]

