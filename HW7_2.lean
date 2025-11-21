import Mathlib.Tactic -- imports all of the tactics in Lean's maths library


set_option autoImplicit false
set_option tactic.hygienic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false


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
-- Problem 2: Analysis of binary search (30 points)
-- ============================================================================

structure SortedArrayFun (n :ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

-- consider the following binary search algorithm on time monad

def contains_bs_monad {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : TimeM (Option ℕ) :=
  bs_aux 0 (n-1)
  where bs_aux (a b :ℕ) (h: a ≤ b := by omega): TimeM (Option ℕ) := do
  if h: a = b then
    if q = arr.get a then return some a
    else return none
  else
    let mid := (a+b)/(2 :ℕ)
    if q < arr.get mid then
      let result ← bs_aux a mid
      ✓ result
    else if  arr.get mid < q then
      let result ← bs_aux (mid+1) b
      ✓ result
    else return (some mid)

-- You can use these two theorems without proof
-- subinterval_to_interval_qlt
-- subinterval_to_interval_qgt

theorem subinterval_to_interval_qlt {n : ℕ} (arr : SortedArrayFun n) (q a mid b : ℕ)
    (h_bounds : a ≤ mid ∧ mid ≤ b)
    (h_q : q < arr.get mid) :
    (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔
      (∃ i, a ≤ i ∧ i ≤ mid ∧ arr.get i = q) := by
  constructor
  · intro h
    rcases h with ⟨i, hia, hib, hi⟩
    have hi_le_mid : i ≤ mid := by
      by_contra hNot
      have hmid_lt : mid < i := lt_of_not_ge hNot
      have hmono := arr.sorted (le_of_lt hmid_lt)
      have hcomp : arr.get mid ≤ arr.get i := hmono
      have : arr.get mid ≤ q := by simpa [hi] using hcomp
      have : arr.get mid < arr.get mid := lt_of_le_of_lt this h_q
      exact lt_irrefl _ this
    exact ⟨i, hia, hi_le_mid, hi⟩
  · intro h
    rcases h with ⟨i, hia, himid, hi⟩
    exact ⟨i, hia, le_trans himid h_bounds.2, hi⟩

theorem subinterval_to_interval_qgt {n : ℕ} (arr : SortedArrayFun n) (q a mid b : ℕ)
    (h_bounds : a ≤ mid ∧ mid ≤ b)
    (h_q : arr.get mid < q) :
    (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔
      (∃ i, mid + 1 ≤ i ∧ i ≤ b ∧ arr.get i = q) := by
  constructor
  · intro h
    rcases h with ⟨i, hia, hib, hi⟩
    have hi_ge_mid_succ : mid + 1 ≤ i := by
      by_contra hNot
      have hi_lt_succ : i < mid + 1 := Nat.lt_of_not_ge hNot
      have hi_le_mid : i ≤ mid := Nat.lt_succ_iff.mp hi_lt_succ
      have hmono := arr.sorted hi_le_mid
      have hcomp : arr.get i ≤ arr.get mid := hmono
      have hle : q ≤ arr.get mid := by simpa [hi] using hcomp
      have hcontr : arr.get mid < arr.get mid := lt_of_lt_of_le h_q hle
      exact lt_irrefl _ hcontr
    exact ⟨i, hi_ge_mid_succ, hib, hi⟩
  · intro h
    rcases h with ⟨i, himid, hib, hi⟩
    have hmid_lt_i : mid < i := lt_of_lt_of_le (Nat.lt_succ_self mid) himid
    have hmid_le_i : mid ≤ i := le_of_lt hmid_lt_i
    have hia : a ≤ i := le_trans h_bounds.1 hmid_le_i
    exact ⟨i, hia, hib, hi⟩



lemma shr_left_m {a b mid : ℕ} (h_le : a ≤ mid) (h_lt : mid < b) :
  mid - a < b - a := by
  have hab : a ≤ b := le_trans h_le (le_of_lt h_lt)
  have hsum : (mid - a) + a < (b - a) + a := by
    simpa [Nat.sub_add_cancel h_le, Nat.sub_add_cancel hab] using h_lt
  exact Nat.lt_of_add_lt_add_right hsum


lemma shr_right_m {a b mid : ℕ}
  (h_lt : a < mid + 1) (h_le : mid + 1 ≤ b) :
  b - (mid + 1) < b - a := by
  have hab : a ≤ b := le_trans (le_of_lt h_lt) h_le
  have h1 : (b - (mid + 1)) + a < (b - (mid + 1)) + (mid + 1) :=
    Nat.add_lt_add_left h_lt (b - (mid + 1))
  have h2 : (b - (mid + 1)) + (mid + 1) = b := Nat.sub_add_cancel h_le
  have h3 : (b - a) + a = b := Nat.sub_add_cancel hab
  have : (b - (mid + 1)) + a < (b - a) + a := by
    simpa [h2, h3] using h1
  exact Nat.lt_of_add_lt_add_right this


lemma left_le_mid_of_le {a b : ℕ} (h : a ≤ b) :
  a ≤ (a + b) / 2 := by
  have h2 : a * 2 ≤ a + b := by
    simpa [Nat.mul_two] using Nat.add_le_add_left h a
  have hpos : 0 < 2 := by decide
  exact (Nat.le_div_iff_mul_le hpos).2 h2

lemma mid_lt_right_of_lt {a b : ℕ} (h : a < b) :
  (a + b) / 2 < b := by
  have hmul : a + b < 2 * b := by
    simpa [two_mul] using add_lt_add_right h b
  exact Nat.div_lt_of_lt_mul hmul


lemma mid_le_right_of_le {a b : ℕ} (h : a ≤ b) :
  (a + b) / 2 ≤ b := by
  have h2 : a + b ≤ 2 * b := by
    simpa [two_mul] using Nat.add_le_add_right h b
  exact Nat.div_le_of_le_mul h2

lemma mid_eq_left_add_half {a b : ℕ} (h : a ≤ b) :
    (a + b) / 2 = a + (b - a) / 2 := by
  have hb : a + (b - a) = b := by
    simpa [Nat.add_comm] using Nat.sub_add_cancel h
  have hsum : a + b = (b - a) + 2 * a := by
    calc
      a + b = a + (a + (b - a)) := by simpa [hb]
      _ = (a + a) + (b - a) := by ac_rfl
      _ = 2 * a + (b - a) := by simp [Nat.two_mul]
      _ = (b - a) + 2 * a := by ac_rfl
  have hdiv := congrArg (fun x : ℕ => x / 2) hsum
  have hsplit :
      ((b - a) + 2 * a) / 2 = a + (b - a) / 2 := by
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using (Nat.add_mul_div_right (b - a) a (by decide : 0 < 2))
  simpa [hsplit] using hdiv


lemma le_pred_iff_lt {i n : ℕ} (hn : 0 < n) :
  i ≤ n - 1 ↔ i < n := by
  have hs : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  constructor
  · intro h
    have : i < (n - 1) + 1 := Nat.lt_succ_of_le h
    simpa [hs] using this
  · intro h
    exact Nat.le_pred_of_lt h


lemma two_mul_add_div_two (s t : ℕ) :
    (2 * s + t) / 2 = s + t / 2 := by
  simpa [Nat.two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]
    using Nat.add_mul_div_right t s (by decide : 0 < 2)


lemma left_len_eq_half {a b : ℕ} (h : a ≤ b) :
    ((a + b) / 2 - a) = (b - a) / 2 := by
  have hmid := mid_eq_left_add_half (a := a) (b := b) h
  have hsub : a ≤ (a + b) / 2 := left_le_mid_of_le h
  have hcalc :
      ((b - a) / 2 + a) - a = (b - a) / 2 := by
    simpa [Nat.add_comm] using
      (Nat.add_sub_cancel ((b - a) / 2) a)
  simpa [hmid, Nat.add_comm, Nat.add_left_comm] using hcalc


lemma left_span_div2 {a b : ℕ} (h : a ≤ b) :
    ((a + b) / 2 - a) ≤ (b - a) / 2 := by
  have : (b - a) / 2 ≤ (b - a) / 2 := le_rfl
  simpa [left_len_eq_half h] using this

lemma sub_half_succ_le_half (Δ : ℕ) :
    Δ - (Δ / 2 + 1) ≤ Δ / 2 := by
  classical
  set k := Δ / 2 with hk
  have hdiv := Nat.mod_add_div Δ 2
  have hmod : Δ % 2 = 0 ∨ Δ % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one Δ
  cases hmod with
  | inl hzero =>
      have hsum :
          Δ = k + k := by
        have : 2 * k = Δ := by
          simpa [hk, hzero] using hdiv
        simpa [two_mul] using this.symm
      have hineq :
          Δ - (k + 1) ≤ Δ - k :=
        Nat.sub_le_sub_left (Nat.le_succ k) Δ
      have hminus : Δ - k = k := by
        simpa [hsum, Nat.add_comm] using Nat.add_sub_cancel k k
      have htarget : Δ - (k + 1) ≤ k := by
        simpa [hminus] using hineq
      simpa [hk] using htarget
  | inr hone =>
      have hsum :
          Δ = k + (k + 1) := by
        have : Δ = 2 * k + 1 := by
          have haux : Δ = Δ % 2 + 2 * k := by
            simpa [hk] using hdiv.symm
          have haux' : Δ = 1 + 2 * k := by
            simpa [hone] using haux
          simpa [Nat.add_comm] using haux'
        simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      have htarget :
          Δ - (k + 1) = k := by
        simpa [hsum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using Nat.add_sub_cancel k (k + 1)
      have : Δ - (k + 1) ≤ k := by simpa [htarget]
      simpa [hk] using this

lemma right_span_div2 {a b : ℕ} (h : a ≤ b) :
    b - ((a + b) / 2 + 1) ≤ (b - a) / 2 := by
  classical
  set Δ := b - a with hΔ
  set mid := (a + b) / 2 with hmid
  have hmid_eq : mid = a + Δ / 2 := by
    simpa [Δ, mid] using mid_eq_left_add_half (a := a) (b := b) h
  have hb : b = a + Δ := by
    have := Nat.sub_add_cancel h
    simpa [Δ, Nat.add_comm, Nat.add_left_comm] using this.symm
  have hcalc :
      b - (mid + 1) = Δ - (Δ / 2 + 1) := by
    have hmid_succ :
        mid + 1 = a + (Δ / 2 + 1) := by
      simp [hmid_eq, Nat.add_assoc, Nat.add_left_comm]
    calc
      b - (mid + 1)
          = (a + Δ) - (mid + 1) := by simpa [hb]
      _ = (a + Δ) - (a + (Δ / 2 + 1)) := by
        simpa [hmid_succ]
      _ = Δ - (Δ / 2 + 1) := by
        simpa using (Nat.add_sub_add_left a Δ (Δ / 2 + 1))
  have := sub_half_succ_le_half Δ
  simpa [Δ, mid, hcalc] using this



def ExistsInRange {n : ℕ} (arr : SortedArrayFun n) (q a b : ℕ) : Prop :=
  ∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q

def StepSpec {n : ℕ} (arr : SortedArrayFun n) (q a b : ℕ) : Prop :=
  if hEq : a = b then
    ExistsInRange arr q a a
  else
    let mid := (a + b) / 2
    if hlt : q < arr.get mid then
      ExistsInRange arr q a mid
    else if hgt : arr.get mid < q then
      ExistsInRange arr q (mid + 1) b
    else
      ExistsInRange arr q a b

lemma step_correct_iff {n : ℕ} (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b) :
  ExistsInRange arr q a b ↔ StepSpec arr q a b := by
  classical
  by_cases hEq : a = b
  · subst hEq
    simp [ExistsInRange, StepSpec]
  ·
    let mid := (a + b) / 2
    have hL : a ≤ mid := left_le_mid_of_le h
    have hR : mid ≤ b := mid_le_right_of_le h
    have hBounds : a ≤ mid ∧ mid ≤ b := ⟨hL, hR⟩
    constructor
    · intro hex
      by_cases hlt : q < arr.get mid
      ·
        have hx :
            (∃ i, a ≤ i ∧ i ≤ mid ∧ arr.get i = q) :=
          (subinterval_to_interval_qlt arr q a mid b hBounds hlt).mp hex
        simpa [StepSpec, hEq, mid, hlt] using hx
      ·
        by_cases hgt : arr.get mid < q
        ·
          have hx :
              (∃ i, (mid+1) ≤ i ∧ i ≤ b ∧ arr.get i = q) :=
            (subinterval_to_interval_qgt arr q a mid b hBounds hgt).mp hex
          simpa [StepSpec, hEq, mid, hlt, hgt] using hx
        ·
          -- equality case
          simpa [StepSpec, hEq, mid, hlt, hgt] using hex
    · intro hstep
      by_cases hlt : q < arr.get mid
      ·
        have hx : ExistsInRange arr q a mid := by
          simpa [StepSpec, hEq, mid, hlt] using hstep
        exact (subinterval_to_interval_qlt arr q a mid b hBounds hlt).mpr hx
      ·
        by_cases hgt : arr.get mid < q
        ·
          have hx : ExistsInRange arr q (mid + 1) b := by
            simpa [StepSpec, hEq, mid, hlt, hgt] using hstep
          exact (subinterval_to_interval_qgt arr q a mid b hBounds hgt).mpr hx
        ·
          -- equality case
          simpa [StepSpec, hEq, mid, hlt, hgt] using hstep
lemma bs_aux_ret_singleton {n : ℕ}
  (arr : SortedArrayFun n) (q a : ℕ) (h : a ≤ a) :
  ((contains_bs_monad.bs_aux arr q a a h).ret ≠ none) ↔ q = arr.get a := by
  classical
  -- Force the a = a branch of bs_aux and split on q = arr.get a
  have hEq : a = a := rfl
  by_cases hq : q = arr.get a
  · simp [contains_bs_monad.bs_aux, hEq, hq]
  · simp [contains_bs_monad.bs_aux, hEq, hq]


lemma bs_aux_time_singleton {n : ℕ}
    (arr : SortedArrayFun n) (q a : ℕ) (h : a ≤ a) :
    (contains_bs_monad.bs_aux arr q a a h).time = 0 := by
  classical
  have hEq : a = a := rfl
  by_cases hq : q = arr.get a
  · simp [contains_bs_monad.bs_aux, hEq, hq]
  · simp [contains_bs_monad.bs_aux, hEq, hq]

@[simp] lemma bs_aux_time_eq_branch_zero {n : ℕ}
    (arr : SortedArrayFun n) (q a : ℕ) :
    (contains_bs_monad.bs_aux arr q a a (le_rfl : a ≤ a)).time = 0 := by
  simpa using bs_aux_time_singleton (arr := arr) (q := q) (a := a) (h := le_rfl)


lemma time_do_tick {α : Type} (m : TimeM α) :
    (do let r ← m; ✓ r : TimeM α).time = m.time + 1 := by
  simp [TimeM.tick]

lemma bs_aux_time_left_branch {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b)
    (hNe : a ≠ b)
    (hlt : q < arr.get ((a + b) / 2)) :
    (contains_bs_monad.bs_aux arr q a b h).time =
      (contains_bs_monad.bs_aux arr q a ((a + b) / 2)
          (left_le_mid_of_le h)).time + 1 := by
  classical
  set mid := (a + b) / 2 with hmid
  have hlt' : q < arr.get mid := by simpa [mid] using hlt
  have hne' : a ≠ b := hNe
  set sub := contains_bs_monad.bs_aux arr q a mid (left_le_mid_of_le h) with hsub
  have htime :
      (contains_bs_monad.bs_aux arr q a b h).time =
        (do let result ← sub; ✓ result : TimeM (Option ℕ)).time := by
    simp [contains_bs_monad.bs_aux, hne', hlt', mid, hsub.symm]
  simpa [sub, time_do_tick] using htime

lemma bs_aux_time_right_branch {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b)
    (hNe : a ≠ b)
    (hlt : ¬ q < arr.get ((a + b) / 2))
    (hgt : arr.get ((a + b) / 2) < q) :
    (contains_bs_monad.bs_aux arr q a b h).time =
      (contains_bs_monad.bs_aux arr q (((a + b) / 2) + 1) b
          (Nat.succ_le_of_lt
            (mid_lt_right_of_lt (lt_of_le_of_ne h hNe)))).time + 1 := by
  classical
  set mid := (a + b) / 2 with hmid
  have hlt' : ¬ q < arr.get mid := by simpa [mid] using hlt
  have hgt' : arr.get mid < q := by simpa [mid] using hgt
  have hne' : a ≠ b := hNe
  have hRight :
      mid + 1 ≤ b := by
    have : mid < b :=
      mid_lt_right_of_lt (lt_of_le_of_ne h hne')
    exact Nat.succ_le_of_lt this
  set sub :=
      contains_bs_monad.bs_aux arr q (mid + 1) b hRight with hsub
  have htime :
      (contains_bs_monad.bs_aux arr q a b h).time =
        (do let result ← sub; ✓ result : TimeM (Option ℕ)).time := by
    simp [contains_bs_monad.bs_aux, hne', hlt', hgt', mid, hsub.symm]
  simpa [sub, mid, time_do_tick] using htime


@[simp] lemma bs_aux_proof_irrel {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ)
    (h₁ h₂ : a ≤ b) :
    contains_bs_monad.bs_aux arr q a b h₁ =
      contains_bs_monad.bs_aux arr q a b h₂ := rfl


lemma neNone_do_tick {α : Type} (m : TimeM (Option α)) :
  ((do let r ← m; ✓ r : TimeM (Option α)).ret ≠ none) ↔ m.ret ≠ none := by
  have hret :
      (do let r ← m; ✓ r : TimeM (Option α)).ret = m.ret := by
    simpa [TimeM.tick] using
      (TimeM.ret_bind m (fun r => TimeM.tick r))
  simpa [hret]


lemma bs_aux_left_branch_neNone_iff {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b)
    (hNe : a ≠ b)
    (hlt : q < arr.get ((a + b) / 2)) :
    ((contains_bs_monad.bs_aux arr q a b h).ret ≠ none) ↔
      ((contains_bs_monad.bs_aux arr q a ((a + b) / 2)
          (left_le_mid_of_le h)).ret ≠ none) := by
  classical
  set mid := (a + b) / 2 with hmid
  have hlt' : q < arr.get mid := by simpa [mid] using hlt
  have hLeft : a ≤ mid := by simpa [mid] using left_le_mid_of_le h
  set sub := contains_bs_monad.bs_aux arr q a mid hLeft with hsub
  have H1 :
      ((contains_bs_monad.bs_aux arr q a b h).ret ≠ none) ↔
        ((do let r ← sub; ✓ r : TimeM (Option ℕ)).ret ≠ none) := by
    simp [contains_bs_monad.bs_aux, hNe, hlt', mid, hsub.symm]
  have H2 :
      ((do let r ← sub; ✓ r : TimeM (Option ℕ)).ret ≠ none) ↔
        sub.ret ≠ none :=
    neNone_do_tick _
  have H := H1.trans H2
  simpa [mid, hsub] using H
  
lemma bs_aux_right_branch_neNone_iff {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b)
    (hNe : a ≠ b)
    (hlt : ¬ q < arr.get ((a + b) / 2))
    (hgt : arr.get ((a + b) / 2) < q) :
    ((contains_bs_monad.bs_aux arr q a b h).ret ≠ none) ↔
      ((contains_bs_monad.bs_aux arr q (((a + b) / 2) + 1) b
          (Nat.succ_le_of_lt
            (mid_lt_right_of_lt (lt_of_le_of_ne h hNe)))).ret ≠ none) := by
  classical
  set mid := (a + b) / 2 with hmid
  have hlt' : ¬ q < arr.get mid := by simpa [mid] using hlt
  have hgt' : arr.get mid < q := by simpa [mid] using hgt
  have hRight : mid + 1 ≤ b := by
    have : mid < b := by
      have : a < b := lt_of_le_of_ne h hNe
      have : (a + b) / 2 < b := mid_lt_right_of_lt this
      simpa [mid] using this
    exact Nat.succ_le_of_lt this
  set sub := contains_bs_monad.bs_aux arr q (mid + 1) b hRight with hsub
  have H1 :
      ((contains_bs_monad.bs_aux arr q a b h).ret ≠ none) ↔
        ((do let r ← sub; ✓ r : TimeM (Option ℕ)).ret ≠ none) := by
    simp [contains_bs_monad.bs_aux, hNe, hlt', hgt', mid, hsub.symm]
  have H2 :
      ((do let r ← sub; ✓ r : TimeM (Option ℕ)).ret ≠ none) ↔
        sub.ret ≠ none :=
    neNone_do_tick _
  have H := H1.trans H2
  simpa [mid, hsub] using H

@[simp] lemma existsInRange_singleton_iff {n : ℕ}
    (arr : SortedArrayFun n) (q a : ℕ) :
  ExistsInRange arr q a a ↔ q = arr.get a := by
  unfold ExistsInRange
  constructor
  · intro ⟨i, hia, hie, hi⟩
    have : i = a := le_antisymm hie hia
    simpa [this] using hi.symm
  · intro hq
    refine ⟨a, le_rfl, le_rfl, ?_⟩
    simpa [hq.symm]

lemma bs_aux_singleton_step {n : ℕ}
  (arr : SortedArrayFun n) (q a : ℕ) (h : a ≤ a) :
  ((contains_bs_monad.bs_aux arr q a a h).ret ≠ none) ↔ StepSpec arr q a a := by
  simpa [StepSpec, existsInRange_singleton_iff arr q a]
    using bs_aux_ret_singleton arr q a h

lemma bs_aux_neNone_of_stepSpec {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b) :
    StepSpec arr q a b →
      (contains_bs_monad.bs_aux arr q a b h).ret ≠ none := by
  classical
  have hRec :
      ∀ k, ∀ {a b : ℕ} (h : a ≤ b), b - a ≤ k →
          StepSpec arr q a b →
            (contains_bs_monad.bs_aux arr q a b h).ret ≠ none := by
    refine Nat.rec ?base ?step
    · intro a b h hdiff hStep
      have hzero : b - a = 0 := le_antisymm hdiff (Nat.zero_le _)
      have hba : b ≤ a := Nat.sub_eq_zero_iff_le.1 hzero
      have hEq : a = b := le_antisymm h hba
      subst hEq
      have hStep' : StepSpec arr q a a := by simpa using hStep
      have hsingle := (bs_aux_singleton_step arr q a le_rfl).mpr hStep'
      simpa using hsingle
    · intro k ih a b h hle hStep
      by_cases hsmall : b - a ≤ k
      · exact ih h hsmall hStep
      ·
        have hdiff : b - a = Nat.succ k := by
          have hlt : k < b - a := Nat.lt_of_not_ge hsmall
          have hsucc : Nat.succ k ≤ b - a := Nat.succ_le_of_lt hlt
          exact le_antisymm hle hsucc
        have hne : a ≠ b := by
          intro hEq; subst hEq
          have : Nat.succ k = 0 := by
            simpa [Nat.sub_self] using hdiff.symm
          exact Nat.succ_ne_zero _ this
        have hlt_ab : a < b := lt_of_le_of_ne h hne
        set mid := (a + b) / 2 with hmid
        have hLeft : a ≤ mid := left_le_mid_of_le h
        have hRight : mid ≤ b := mid_le_right_of_le h
        have hmid_lt_b : mid < b := mid_lt_right_of_lt hlt_ab
        dsimp [StepSpec] at hStep
        split_ifs at hStep with hEq' hlt hgt
        · exact (hne hEq').elim
        ·
          have hx : ExistsInRange arr q a mid := by simpa [hmid] using hStep
          have hSub : StepSpec arr q a mid :=
            (step_correct_iff arr q a mid hLeft).mp hx
          have hmeasure_lt : mid - a < b - a := shr_left_m hLeft hmid_lt_b
          have hmeasure_le : mid - a ≤ k := by
            have : mid - a < Nat.succ k := by simpa [hdiff] using hmeasure_lt
            exact Nat.lt_succ_iff.mp this
          have hind := ih hLeft hmeasure_le hSub
          exact
            (bs_aux_left_branch_neNone_iff arr q a b h hne hlt).2 hind
        ·
          have hx : ExistsInRange arr q (mid + 1) b := by
            simpa [hmid] using hStep
          have hRight' : mid + 1 ≤ b := Nat.succ_le_of_lt hmid_lt_b
          have hSub : StepSpec arr q (mid + 1) b :=
            (step_correct_iff arr q (mid + 1) b hRight').mp hx
          have ha_lt_mid_succ : a < mid + 1 := Nat.lt_succ_of_le hLeft
          have hmeasure_lt : b - (mid + 1) < b - a :=
            shr_right_m ha_lt_mid_succ hRight'
          have hmeasure_le : b - (mid + 1) ≤ k := by
            have : b - (mid + 1) < Nat.succ k := by simpa [hdiff] using hmeasure_lt
            exact Nat.lt_succ_iff.mp this
          have hind := ih hRight' hmeasure_le hSub
          exact
            (bs_aux_right_branch_neNone_iff arr q a b h hne hlt hgt).2 hind
        ·
          have hEqMid : q = arr.get mid :=
            le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
          simpa [contains_bs_monad.bs_aux, hEq', hmid, hlt, hgt, hEqMid]
            using (neNone_return_some mid)
  intro hStep
  exact hRec (b - a) h (Nat.le_refl _) hStep


@[simp] lemma ret_do_tick {α : Type} (m : TimeM α) :
  (do let r ← m; ✓ r : TimeM α).ret = m.ret := by
  simpa [TimeM.tick] using (TimeM.ret_bind m (fun r => TimeM.tick r))

@[simp] lemma neNone_return_some {α : Type} (x : α) :
  ((return (some x) : TimeM (Option α)).ret ≠ none) := by
  simp


lemma bs_aux_ret_neNone_implies_stepSpec {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b) :
    ((contains_bs_monad.bs_aux arr q a b h).ret ≠ none) →
      StepSpec arr q a b := by
  classical
  have hRec :
      ∀ k, ∀ {a b : ℕ} (h : a ≤ b), b - a ≤ k →
          ((contains_bs_monad.bs_aux arr q a b h).ret ≠ none) →
            StepSpec arr q a b := by
    refine Nat.rec ?base ?step
    · intro a b h hdiff hret
      have hzero : b - a = 0 := le_antisymm hdiff (Nat.zero_le _)
      have hba : b ≤ a := Nat.sub_eq_zero_iff_le.1 hzero
      have hEq : a = b := le_antisymm h hba
      subst hEq
      have := (bs_aux_singleton_step arr q a le_rfl).1 hret
      simpa using this
    · intro k ih a b h hle hret
      by_cases hsmall : b - a ≤ k
      · exact ih h hsmall hret
      ·
        have hdiff : b - a = Nat.succ k := by
          have hlt : k < b - a := Nat.lt_of_not_ge hsmall
          have hsucc : Nat.succ k ≤ b - a := Nat.succ_le_of_lt hlt
          exact le_antisymm hle hsucc
        have hne : a ≠ b := by
          intro hEq; subst hEq
          have : Nat.succ k = 0 := by
            simpa [Nat.sub_self] using hdiff.symm
          exact Nat.succ_ne_zero _ this
        have hlt_ab : a < b := lt_of_le_of_ne h hne
        set mid := (a + b) / 2 with hmid
        have hLeft : a ≤ mid := left_le_mid_of_le h
        have hRight : mid ≤ b := mid_le_right_of_le h
        have hmid_lt_b : mid < b := mid_lt_right_of_lt hlt_ab
        by_cases hlt : q < arr.get mid
        ·
          have hRetSub :
              (contains_bs_monad.bs_aux arr q a mid hLeft).ret ≠ none :=
            (bs_aux_left_branch_neNone_iff arr q a b h hne hlt).1 hret
          have hmeasure_lt : mid - a < b - a := shr_left_m hLeft hmid_lt_b
          have hmeasure_le : mid - a ≤ k := by
            have : mid - a < Nat.succ k := by simpa [hdiff] using hmeasure_lt
            exact Nat.lt_succ_iff.mp this
          have hStepSub := ih hLeft hmeasure_le hRetSub
          have hExists : ExistsInRange arr q a mid :=
            (step_correct_iff arr q a mid hLeft).mpr hStepSub
          have hEq' : a ≠ b := hne
          have hlt' : q < arr.get ((a + b) / 2) := by simpa [hmid] using hlt
          simpa [StepSpec, hEq', hmid, hlt'] using hExists
        ·
          by_cases hgt : arr.get mid < q
          ·
            have hRetSub :
                (contains_bs_monad.bs_aux arr q (mid + 1) b
                    (Nat.succ_le_of_lt hmid_lt_b)).ret ≠ none :=
              (bs_aux_right_branch_neNone_iff arr q a b h hne
                (by simpa [hmid] using hlt) (by simpa [hmid] using hgt)).1 hret
            have hRight' : mid + 1 ≤ b := Nat.succ_le_of_lt hmid_lt_b
            have ha_lt_mid_succ : a < mid + 1 := Nat.lt_succ_of_le hLeft
            have hmeasure_lt : b - (mid + 1) < b - a :=
              shr_right_m ha_lt_mid_succ hRight'
            have hmeasure_le : b - (mid + 1) ≤ k := by
              have : b - (mid + 1) < Nat.succ k := by simpa [hdiff] using hmeasure_lt
              exact Nat.lt_succ_iff.mp this
            have hStepSub := ih hRight' hmeasure_le hRetSub
            have hExists : ExistsInRange arr q (mid + 1) b :=
              (step_correct_iff arr q (mid + 1) b hRight').mpr hStepSub
            have hEq' : a ≠ b := hne
            have hlt' : ¬ q < arr.get ((a + b) / 2) := by
              simpa [hmid] using hlt
            have hgt' : arr.get ((a + b) / 2) < q := by
              simpa [hmid] using hgt
            simpa [StepSpec, hEq', hmid, hlt', hgt'] using hExists
          ·
            have hEqMid : q = arr.get mid :=
              le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
            have hExists : ExistsInRange arr q a b := by
              refine ⟨mid, hLeft, hRight, ?_⟩
              simpa [hEqMid]
            have hEq' : a ≠ b := hne
            have hlt' : ¬ q < arr.get ((a + b) / 2) := by
              simpa [hmid] using hlt
            have hgt' : ¬ arr.get ((a + b) / 2) < q := by
              simpa [hmid] using hgt
            simpa [StepSpec, hEq', hmid, hlt', hgt'] using hExists
  intro hret
  exact hRec (b - a) h (Nat.le_refl _) hret


lemma bs_aux_ret_neNone_iff_stepSpec {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b) :
    ((contains_bs_monad.bs_aux arr q a b h).ret ≠ none) ↔
      StepSpec arr q a b := by
  constructor
  · exact bs_aux_ret_neNone_implies_stepSpec arr q a b h
  · exact bs_aux_neNone_of_stepSpec arr q a b h


@[simp] lemma existsInRange_zero_pred_iff {n : ℕ}
    (arr : SortedArrayFun n) (q : ℕ) (hn : 0 < n) :
  ExistsInRange arr q 0 (n - 1) ↔ ∃ i, i < n ∧ arr.get i = q := by
  unfold ExistsInRange
  constructor
  · intro ⟨i, _h0, hi, hq⟩
    have hi' : i < n := (le_pred_iff_lt (i := i) (n := n) hn).1 hi
    exact ⟨i, hi', hq⟩
  · intro ⟨i, hi, hq⟩
    have hi' : i ≤ n - 1 := (le_pred_iff_lt (i := i) (n := n) hn).2 hi
    exact ⟨i, Nat.zero_le _, hi', hq⟩

@[simp] lemma stepSpec_top_iff {n : ℕ}
    (arr : SortedArrayFun n) (q : ℕ) (hn : 0 < n) :
  StepSpec arr q 0 (n - 1) ↔ ∃ i, i < n ∧ arr.get i = q := by
  calc
    StepSpec arr q 0 (n - 1)
        ↔ ExistsInRange arr q 0 (n - 1) := by
             simpa using
               (step_correct_iff arr q 0 (n - 1) (Nat.zero_le _)).symm
    _   ↔ ∃ i, i < n ∧ arr.get i = q := existsInRange_zero_pred_iff arr q hn





-- # (10 Points) Problem 2.1: Prove the correctness of this algorithm.
-- Hint: Your solution should be minimally changed from the non-monad version
theorem Problem2_part1 (n q :ℕ)(h: 0 < n)(arr : SortedArrayFun n):
  (∃ i, i < n ∧ arr.get i = q) ↔ ((contains_bs_monad arr q).ret ≠ none) := by
  classical
  have hStepExists := stepSpec_top_iff (arr := arr) (q := q) h
  have h0 : 0 ≤ n - 1 := Nat.zero_le _
  have hRetStep :
      ((contains_bs_monad arr q).ret ≠ none) ↔
        StepSpec arr q 0 (n - 1) := by
    dsimp [contains_bs_monad]
    simpa [bs_aux_proof_irrel, h0]
      using (bs_aux_ret_neNone_iff_stepSpec (arr := arr) (q := q)
        (a := 0) (b := n - 1) h0)
  constructor
  · intro hex
    have hStep : StepSpec arr q 0 (n - 1) := hStepExists.mpr hex
    exact (hRetStep.mpr hStep)
  · intro hret
    have hStep : StepSpec arr q 0 (n - 1) := hRetStep.mp hret
    exact hStepExists.mp hStep




-- Next, we will prove the running time
def g (n : ℕ) : ℕ :=
  if n = 0 then 0
  else g (n/2) + 1

@[simp] lemma g_zero : g 0 = 0 := by
  unfold g
  split_ifs with h
  · rfl
  · exact (h rfl).elim

lemma g_recurrence {n : ℕ} (hn : n ≠ 0) :
    g n = g (n / 2) + 1 := by
  classical
  conv_lhs => unfold g
  exact if_neg hn

lemma div_two_eq_zero_iff_lt_two (n : ℕ) :
    n / 2 = 0 ↔ n < 2 := by
  constructor
  · intro h
    have : ¬ 2 ≤ n := by
      intro hge
      have hpos : 0 < n / 2 := Nat.div_pos hge (by decide : 0 < 2)
      exact (ne_of_gt hpos) h
    exact lt_of_not_ge this
  · intro h
    exact Nat.div_eq_of_lt h

lemma g_eq_log_formula :
    ∀ n : ℕ, g n = (if n = 0 then 0 else Nat.log 2 n + 1) := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n IH
  by_cases hn : n = 0
  · subst hn
    simp [g_zero]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hrec := g_recurrence (n := n) hn
    have hlt : n / 2 < n := Nat.div_lt_self hpos (by decide : 1 < 2)
    have hIH := IH (n / 2) hlt
    have hgn :
        g n = (if n / 2 = 0 then 0 else Nat.log 2 (n / 2) + 1) + 1 := by
      simpa [hIH]
        using hrec
    by_cases hz : n / 2 = 0
    · have hn_one : n = 1 := by
        have hn_lt_two : n < 2 := (div_two_eq_zero_iff_lt_two n).1 hz
        have hn_le_one : n ≤ 1 := Nat.lt_succ_iff.mp hn_lt_two
        have hn_ge_one : 1 ≤ n := Nat.succ_le_of_lt hpos
        exact le_antisymm hn_le_one hn_ge_one
      subst hn_one
      simp [hgn, hz, Nat.log_one_right]
    · have hzpos : 2 ≤ n := by
        have : ¬ n < 2 := by
          intro hlt
          exact hz ((div_two_eq_zero_iff_lt_two n).2 hlt)
        exact Nat.le_of_not_gt this
      have hlog :
          Nat.log 2 n = Nat.log 2 (n / 2) + 1 :=
        Nat.log_of_one_lt_of_le (b := 2) (n := n) (by decide : 1 < 2) hzpos
      have hgn' :
          g n = (Nat.log 2 (n / 2) + 1) + 1 := by
        have := hgn
        rw [if_neg hz] at this
        simpa using this
      have hrhs :
          Nat.log 2 n + 1 = (Nat.log 2 (n / 2) + 1) + 1 := by
        have := congrArg (fun t => t + 1) hlog
        simpa using this
      have hgoal :
          g n = Nat.log 2 n + 1 := by
        simpa [hgn', hrhs, add_comm, add_left_comm, add_assoc]
      simpa [hn, hgoal]

lemma g_pos_eq {n : ℕ} (hn : n ≠ 0) :
    g n = Nat.log 2 n + 1 := by
  have := g_eq_log_formula n
  simpa [hn] using this

theorem g_close_form (n : ℕ) : g n ≤  Nat.log 2 n + 1 := by
  by_cases hn : n = 0
  · subst hn
    simp [g_zero]
  · have h := g_pos_eq (n := n) hn
    simpa [h] using (Nat.le_refl (Nat.log 2 n + 1))

theorem g_monotone : Monotone g := by
  intro a b h
  by_cases ha : a = 0
  · subst ha
    simpa [g_zero] using Nat.zero_le _
  · have hb : b ≠ 0 := by
      have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
      exact ne_of_gt (lt_of_lt_of_le ha_pos h)
    have hga := g_pos_eq (n := a) ha
    have hgb := g_pos_eq (n := b) hb
    have hlog : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_monotone h
    have : Nat.log 2 a + 1 ≤ Nat.log 2 b + 1 := add_le_add_right hlog 1
    simpa [hga, hgb] using this

lemma bs_aux_time_left_bound {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b)
    (hNe : a ≠ b)
    (hlt : q < arr.get ((a + b) / 2))
    (hSub :
      (contains_bs_monad.bs_aux arr q a ((a + b) / 2)
          (left_le_mid_of_le h)).time ≤
        g (((a + b) / 2) - a)) :
    (contains_bs_monad.bs_aux arr q a b h).time ≤
      g ((b - a) / 2) + 1 := by
  have htime :=
    bs_aux_time_left_branch (arr := arr) (q := q)
      (a := a) (b := b) (h := h) hNe hlt
  have hsucc :
      (contains_bs_monad.bs_aux arr q a ((a + b) / 2)
          (left_le_mid_of_le h)).time + 1 ≤
        g (((a + b) / 2) - a) + 1 :=
    Nat.succ_le_succ hSub
  have hmono :
      g (((a + b) / 2) - a) ≤ g ((b - a) / 2) :=
    g_monotone (left_span_div2 h)
  have hmono_succ :
      g (((a + b) / 2) - a) + 1 ≤ g ((b - a) / 2) + 1 :=
    Nat.succ_le_succ hmono
  have hbound :
      (contains_bs_monad.bs_aux arr q a ((a + b) / 2)
          (left_le_mid_of_le h)).time + 1 ≤
        g ((b - a) / 2) + 1 :=
    hsucc.trans hmono_succ
  simpa [htime] using hbound

lemma bs_aux_time_right_bound {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b)
    (hNe : a ≠ b)
    (hlt : ¬ q < arr.get ((a + b) / 2))
    (hgt : arr.get ((a + b) / 2) < q)
    (hSub :
      (contains_bs_monad.bs_aux arr q (((a + b) / 2) + 1) b
          (Nat.succ_le_of_lt
            (mid_lt_right_of_lt (lt_of_le_of_ne h hNe)))).time ≤
        g (b - (((a + b) / 2) + 1))) :
    (contains_bs_monad.bs_aux arr q a b h).time ≤
      g ((b - a) / 2) + 1 := by
  have htime :=
    bs_aux_time_right_branch (arr := arr) (q := q)
      (a := a) (b := b) (h := h) hNe hlt hgt
  have hsucc :
      (contains_bs_monad.bs_aux arr q (((a + b) / 2) + 1) b
          (Nat.succ_le_of_lt
            (mid_lt_right_of_lt (lt_of_le_of_ne h hNe)))).time + 1 ≤
        g (b - (((a + b) / 2) + 1)) + 1 :=
    Nat.succ_le_succ hSub
  have hmono :
      g (b - (((a + b) / 2) + 1)) ≤ g ((b - a) / 2) :=
    g_monotone (right_span_div2 h)
  have hmono_succ :
      g (b - (((a + b) / 2) + 1)) + 1 ≤ g ((b - a) / 2) + 1 :=
    Nat.succ_le_succ hmono
  have hbound :
      (contains_bs_monad.bs_aux arr q (((a + b) / 2) + 1) b
          (Nat.succ_le_of_lt
            (mid_lt_right_of_lt (lt_of_le_of_ne h hNe)))).time + 1 ≤
        g ((b - a) / 2) + 1 :=
    hsucc.trans hmono_succ
  simpa [htime] using hbound

-- # (20 Points) Problem 2.2: Prove the running time of this algorithm.
-- Hint: Formulate an intermediate lemma that works for general range [a,b] and then specialize to [0, n-1] to prove this

private lemma bs_aux_time_le_g_aux {n : ℕ}
    (arr : SortedArrayFun n) (q : ℕ) :
    ∀ k, ∀ {a b : ℕ} (h : a ≤ b), b - a ≤ k →
        (contains_bs_monad.bs_aux arr q a b h).time ≤ g (b - a) := by
  classical
  refine Nat.rec ?base ?step
  · intro a b h hdiff
    have hzero : b - a = 0 := le_antisymm hdiff (Nat.zero_le _)
    have hba : b ≤ a := Nat.sub_eq_zero_iff_le.1 hzero
    have hEq : a = b := le_antisymm h hba
    subst hEq
    simpa [bs_aux_time_eq_branch_zero, g_zero]
  · intro k ih a b h hle
    by_cases hsmall : b - a ≤ k
    · exact ih h hsmall
    ·
      have hdiff : b - a = Nat.succ k := by
        have hlt : k < b - a := Nat.lt_of_not_ge hsmall
        have hsucc : Nat.succ k ≤ b - a := Nat.succ_le_of_lt hlt
        exact le_antisymm hle hsucc
      have hne : a ≠ b := by
        intro hEq; subst hEq
        simpa [Nat.sub_self] using hdiff
      have hlt_ab : a < b := lt_of_le_of_ne h hne
      set mid := (a + b) / 2 with hmid
      have hLeft : a ≤ mid := left_le_mid_of_le h
      have hRight : mid ≤ b := mid_le_right_of_le h
      have hmid_lt_b : mid < b := mid_lt_right_of_lt hlt_ab
      have hΔpos : b - a ≠ 0 := by
        simpa [hdiff]
      have hgrec := g_recurrence hΔpos
      by_cases hlt : q < arr.get mid
      ·
        have hmeasure_lt : mid - a < b - a := shr_left_m hLeft hmid_lt_b
        have hmeasure_le : mid - a ≤ k := by
          have : mid - a < Nat.succ k := by simpa [hdiff] using hmeasure_lt
          exact Nat.lt_succ_iff.1 this
        have hSub := ih hLeft hmeasure_le
        have hbound :=
          bs_aux_time_left_bound (arr := arr) (q := q)
            (a := a) (b := b) (h := h) hne hlt hSub
        have hgoal :
            (contains_bs_monad.bs_aux arr q a b h).time ≤ g (b - a) := by
          simpa [hgrec] using hbound
        exact hgoal
      ·
        by_cases hgt : arr.get mid < q
        ·
          have hRight' : mid + 1 ≤ b := Nat.succ_le_of_lt hmid_lt_b
          have ha_lt_mid_succ : a < mid + 1 := Nat.lt_succ_of_le hLeft
          have hmeasure_lt :
              b - (mid + 1) < b - a :=
            shr_right_m ha_lt_mid_succ hRight'
          have hmeasure_le : b - (mid + 1) ≤ k := by
            have : b - (mid + 1) < Nat.succ k := by
              simpa [hdiff] using hmeasure_lt
            exact Nat.lt_succ_iff.1 this
          have hSub :=
            ih hRight' hmeasure_le
          have hbound :=
            bs_aux_time_right_bound (arr := arr) (q := q)
              (a := a) (b := b) (h := h) hne hlt hgt hSub
          have hgoal :
              (contains_bs_monad.bs_aux arr q a b h).time ≤ g (b - a) := by
            simpa [hgrec] using hbound
          exact hgoal
        ·
          have hEqMid : q = arr.get mid :=
            le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
          have htime_zero :
              (contains_bs_monad.bs_aux arr q a b h).time = 0 := by
            simp [contains_bs_monad.bs_aux, hne, hlt, hgt, hEqMid, mid]
          have hgoal :
              (contains_bs_monad.bs_aux arr q a b h).time ≤ g (b - a) := by
            simpa [htime_zero] using (Nat.zero_le (g (b - a)))
          exact hgoal

lemma bs_aux_time_le_g {n : ℕ}
    (arr : SortedArrayFun n) (q a b : ℕ) (h : a ≤ b) :
    (contains_bs_monad.bs_aux arr q a b h).time ≤ g (b - a) :=
  bs_aux_time_le_g_aux (arr := arr) (q := q) (k := b - a) h (Nat.le_refl _)

lemma contains_time_le_g {n : ℕ} (arr : SortedArrayFun n) (q : ℕ) :
    (contains_bs_monad arr q).time ≤ g (n - 1) := by
  classical
  have h0 : 0 ≤ n - 1 := Nat.zero_le _
  dsimp [contains_bs_monad]
  simpa [bs_aux_proof_irrel, h0]
    using (bs_aux_time_le_g (arr := arr) (q := q)
      (a := 0) (b := n - 1) (h := h0))

theorem Problem2_part2 (n q :ℕ) (arr : SortedArrayFun n) :
    (contains_bs_monad arr q).time ≤ Nat.log 2 (n - 1) + 1 := by
  have htime := contains_time_le_g (arr := arr) (q := q)
  exact htime.trans (g_close_form (n - 1))
