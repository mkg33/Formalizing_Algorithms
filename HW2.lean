import Mathlib.Tactic
import Mathlib.Data.Nat.Log
set_option autoImplicit false
set_option tactic.hygienic false

/-
  Problem 1
-/
def SumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => SumOdd n + (2*n + 1)

theorem P1 (n : ℕ) : SumOdd n = n^2 := by
  induction' n with n ih
  · simp [SumOdd]
  ·
    simp [SumOdd, ih, pow_two, Nat.succ_mul, Nat.mul_succ, two_mul,
          add_comm, add_left_comm, add_assoc]

/-
  Problems 2 and 3
-/
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
notation:10000 n "!" => factorial n

def isEven (n : ℕ) : Prop := ∃ k, n = 2*k

/-- `2*k = 1`, impossible in `ℕ`. -/
lemma two_mul_ne_one (k : ℕ) : 2 * k ≠ 1 := by
  cases k with
  | zero => simp
  | succ k =>
      have h : 1 + 1 ≤ (k + 1) + (k + 1) := by
        exact Nat.add_le_add (Nat.succ_le_succ (Nat.zero_le k)) (Nat.succ_le_succ (Nat.zero_le k))
      have h2 : 2 ≤ 2 * (k + 1) := by
        simpa [two_mul] using h
      exact ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) h2)

lemma not_isEven_one : ¬ isEven 1 := by
  rintro ⟨k, hk⟩
  exact two_mul_ne_one k hk.symm

/-- If `a` even, then `b*a` even. -/
lemma isEven_mul_left {a b : ℕ} (h : isEven a) : isEven (b * a) := by
  rcases h with ⟨k, hk⟩
  refine ⟨b * k, ?_⟩
  simp [hk, Nat.mul_comm, Nat.mul_assoc]

/-- For all `m`, `(m+2)!` is even. -/
lemma factorial_even_add_two (m : ℕ) : isEven ((m + 2)!) := by
  induction' m with m ih
  · exact ⟨1, by simp [factorial]⟩
  ·
    simpa [factorial] using
      isEven_mul_left (a := (m + 2)!) (b := m + 3) ih


theorem P2 (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by
  constructor
  · intro h
    cases' n with n
    ·
      have h1 := h
      simp [factorial] at h1
      exact (not_isEven_one h1).elim
    · cases' n with n
      ·
        have h1 := h
        simp [factorial] at h1
        exact (not_isEven_one h1).elim
      ·
        exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
  · intro hn
    have hsplit : n = (n - 2) + 2 := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.sub_add_cancel hn).symm
    rcases factorial_even_add_two (n - 2) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [hsplit.symm] using hk

/-
  Problem 3
  To prove: ∀ n > 0, 3^n > n^2
-/


lemma succ_sq_le_three_mul_sq_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    (n + 1)^2 ≤ 3 * n^2 := by
  have h1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn
  have h2 : 1 ≤ n - 1 := by
    simpa using (Nat.sub_le_sub_right hn 1)
  have hNat : 2 ≤ (2 * n) * (n - 1) := by
    have hL : 2 ≤ 2 * n := by
      have : 2 * 1 ≤ 2 * n := Nat.mul_le_mul_left 2 h1
      simpa using this
    have : 2 * 1 ≤ (2 * n) * (n - 1) := Nat.mul_le_mul hL h2
    simpa using this
  -- zify the Nat inequality into ℤ
  have hInt₀ : (2 : ℤ) ≤ (2 : ℤ) * (n : ℤ) * ((n - 1 : ℕ) : ℤ) := by
    zify at hNat
    simpa using hNat
  -- cast of (n - 1)
  have cast_sub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    simpa using (Nat.cast_sub (R := ℤ) h1)
  have hInt : (2 : ℤ) ≤ 2 * (n : ℤ) * ((n : ℤ) - 1) := by
    simpa [cast_sub, mul_comm, mul_left_comm, mul_assoc] using hInt₀
  have hge0 : 0 ≤ 2 * (n : ℤ) * ((n : ℤ) - 1) - 1 := by
    have : (1 : ℤ) ≤ 2 * (n : ℤ) * ((n : ℤ) - 1) :=
      le_trans (by norm_num : (1 : ℤ) ≤ 2) hInt
    exact sub_nonneg.mpr this
  have hdiff :
      3 * (n : ℤ)^2 - ((n + 1 : ℤ)^2)
        = 2 * (n : ℤ) * ((n : ℤ) - 1) - 1 := by
    ring
  have : ((n + 1)^2 : ℤ) ≤ 3 * (n : ℤ)^2 := by
    have : 0 ≤ 3 * (n : ℤ)^2 - ((n + 1 : ℤ)^2) := by
      simpa [hdiff] using hge0
    linarith
  exact_mod_cast this

lemma pow3_gt_sq_ge_two : ∀ k, 3 ^ (k + 2) > (k + 2) ^ 2 := by
  intro k
  induction' k with k ih
  · decide
  ·
    have hmul :
        3 * ((k + 2) ^ 2) < 3 * (3 ^ (k + 2)) :=
      Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 3)
    have hk : 2 ≤ k + 2 :=
      Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
    have hbound :
        (k + 3) ^ 2 ≤ 3 * (k + 2) ^ 2 := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        succ_sq_le_three_mul_sq_of_two_le (k + 2) hk
    have hlt := lt_of_le_of_lt hbound hmul
    simpa [pow_succ, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt

theorem P3 : ∀ n > 0 , 3 ^ n > n ^ 2 := by
  intro n hn
  cases' n with n
  · cases hn
  · cases' n with n
    · decide
    · simpa using pow3_gt_sq_ge_two n

/-
  Problem 4
  g(0)=0, g(n+1)=g((n+1)/2)+1. Show g(n) ≤ log₂ n + 1. This is the same statement as in the problem sheet, I'm just using the n+1 form.
-/
def g : ℕ → ℕ
  | 0     => 0
  | n + 1 => g ((n + 1) / 2) + 1
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

theorem g_le_log_add_one : ∀ n, g n ≤ Nat.log 2 n + 1 := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro n IH
  cases' n with n
  · simp [g]
  · cases' n with n
    · simp [g]
    ·
      have IH' : g ((n + 2) / 2) ≤ Nat.log 2 ((n + 2) / 2) + 1 :=
        IH ((n + 2) / 2) (Nat.div_lt_self (Nat.succ_pos _) (by decide))
      have half_ge_one : 1 ≤ ((n + 2) / 2) := by
        have h2 : 2 ≤ n + 2 :=
          Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
        have h12 : 1 * 2 ≤ n + 2 := by
          change 2 ≤ n + 2
          exact h2
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 h12
      have half_pos : 0 < ((n + 2) / 2) :=
        lt_of_lt_of_le (by decide : 0 < 1) half_ge_one
      have pow_le_half :
          2 ^ Nat.log 2 ((n + 2) / 2) ≤ ((n + 2) / 2) :=
        (Nat.pow_le_iff_le_log (by decide : 1 < 2) (by exact ne_of_gt half_pos)).2 le_rfl
      have pow_le : 2 ^ (Nat.log 2 ((n + 2) / 2) + 1) ≤ n + 2 := by
        calc
          2 ^ (Nat.log 2 ((n + 2) / 2) + 1)
              = 2 ^ Nat.log 2 ((n + 2) / 2) * 2 := by
                simp [pow_succ, Nat.mul_comm]
          _ ≤ ((n + 2) / 2) * 2 := Nat.mul_le_mul_right _ pow_le_half
          _ ≤ n + 2 := by
                simpa [Nat.mul_comm] using
                  (Nat.div_mul_le_self (n + 2) 2)
      have stepLog :
          Nat.log 2 ((n + 2) / 2) + 1 ≤ Nat.log 2 (n + 2) :=
        Nat.le_log_of_pow_le (by decide : 1 < 2) pow_le
      have step2 :
          (Nat.log 2 ((n + 2) / 2) + 1) + 1 ≤ Nat.log 2 (n + 2) + 1 :=
        Nat.add_le_add_right stepLog 1
      have g_eq : g (n + 2) = g ((n + 2) / 2) + 1 := by
        simp [g, Nat.add_comm, Nat.add_left_comm]
      have hA : g (n + 2)
            ≤ (Nat.log 2 ((n + 2) / 2) + 1) + 1 := by
        have h := Nat.add_le_add_right IH' 1
        simpa [g_eq] using h
      exact le_trans hA step2

/-
  Problem 5
  Recurrence on ℕ: f(n) = 2*f(n-1) - f(n-2) + 2,  f(0)=1, f(1)=1
  Claim: f(n) = n^2 - n + 1
-/
/- Problem 5: `f(0)=1`, `f(1)=1`, `f(n+2)=2*f(n+1)-f(n)+2`. -/
def f : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 2 => 2 * f (n + 1) - f n + 2

theorem P5 (n : ℕ) : f n = n^2 - n + 1 := by
  refine Nat.strong_induction_on n ?_
  intro n IH
  cases' n with n
  · simp [f]
  · cases' n with n
    · simp [f]
    ·
      have ih0 : f n = n^2 - n + 1 :=
        IH n (Nat.add_lt_add_left (Nat.succ_pos 1) n)
      have ih1 : f (n + 1) = (n + 1)^2 - (n + 1) + 1 :=
        IH (n + 1) (Nat.add_lt_add_left (Nat.succ_lt_succ Nat.zero_lt_one) n)

      have hle_n_sq : n ≤ n^2 := by
        cases' n with k
        · simp
        ·
          have hx :=
            Nat.mul_le_mul_left (k.succ) (Nat.succ_le_succ (Nat.zero_le k))
          calc
            k.succ = k.succ * 1 := by simp
            _ ≤ k.succ * k.succ := by exact hx
            _ = (k.succ) ^ 2 := by simp [pow_two]
      have ih0z : (f n : ℤ) = (n : ℤ)^2 - (n : ℤ) + 1 := by
        have hcast := congrArg (fun x : ℕ => (x : ℤ)) ih0
        have hsub : ((n^2 - n : ℕ) : ℤ) = (n : ℤ)^2 - (n : ℤ) := by
          simpa [Nat.cast_pow] using (Nat.cast_sub (R := ℤ) hle_n_sq)
        simpa [Nat.cast_add, Nat.cast_one, hsub] using hcast

      have hle_succ_sq : n + 1 ≤ (n + 1)^2 := by
        have hx :=
          Nat.mul_le_mul_left (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n))
        calc
          n + 1 = (n + 1) * 1 := by simp
          _ ≤ (n + 1) * (n + 1) := by exact hx
          _ = (n + 1) ^ 2 := by simp [pow_two]
      have ih1z : (f (n + 1) : ℤ) = ((n + 1 : ℤ))^2 - (n + 1 : ℤ) + 1 := by
        have hcast := congrArg (fun x : ℕ => (x : ℤ)) ih1
        have hsub : (((n + 1)^2 - (n + 1) : ℕ) : ℤ)
              = ((n + 1 : ℤ))^2 - (n + 1 : ℤ) := by
          simpa [Nat.cast_pow] using (Nat.cast_sub (R := ℤ) hle_succ_sq)
        simpa [Nat.cast_add, Nat.cast_one, hsub] using hcast

      have guard : f n ≤ 2 * f (n + 1) := by
        zify
        have hpoly_nonneg :
            0 ≤ 2 * (((n + 1 : ℤ))^2 - (n + 1 : ℤ) + 1)
                - ((n : ℤ)^2 - (n : ℤ) + 1) := by
          have hrewrite :
              2 * (((n + 1 : ℤ))^2 - (n + 1 : ℤ) + 1)
                - ((n : ℤ)^2 - (n : ℤ) + 1)
                = (n : ℤ)^2 + 3 * (n : ℤ) + 1 := by
            ring
          have hz2 : 0 ≤ (n : ℤ)^2 := sq_nonneg (n : ℤ)
          have hz3 : 0 ≤ 3 * (n : ℤ) :=
            mul_nonneg (by decide : 0 ≤ (3 : ℤ)) (by exact_mod_cast Nat.zero_le n)
          have : 0 ≤ (n : ℤ)^2 + 3 * (n : ℤ) + 1 :=
            add_nonneg (add_nonneg hz2 hz3) (by decide : 0 ≤ (1 : ℤ))
          simpa [hrewrite] using this
        have : 0 ≤ 2 * (f (n + 1) : ℤ) - (f n : ℤ) := by
          simpa [ih1z, ih0z] using hpoly_nonneg
        exact (sub_nonneg.mp this)

      have recZ : (f (n + 2) : ℤ)
          = 2 * (f (n + 1) : ℤ) - (f n : ℤ) + 2 := by
        have hdef : f (n + 2) = 2 * f (n + 1) - f n + 2 := rfl
        have hcast : (f (n + 2) : ℤ)
              = ((2 * f (n + 1) - f n : ℕ) : ℤ) + 2 := by
          simpa [Nat.cast_add] using congrArg (fun x : ℕ => (x : ℤ)) hdef
        have hsub : ((2 * f (n + 1) - f n : ℕ) : ℤ)
              = 2 * (f (n + 1) : ℤ) - (f n : ℤ) := by
          simpa [Nat.cast_mul] using (Nat.cast_sub (R := ℤ) guard)
        simpa [hsub] using hcast

      have recZ' : (f (n + 2) : ℤ)
            = 2 * (((n + 1 : ℤ))^2 - (n + 1 : ℤ) + 1)
                - ((n : ℤ)^2 - (n : ℤ) + 1) + 2 := by
        simpa [ih1z, ih0z] using recZ
      have eqZ : (f (n + 2) : ℤ)
              = ((n + 2 : ℤ))^2 - (n + 2 : ℤ) + 1 := by
        have hpoly :
            2 * (((n + 1 : ℤ))^2 - (n + 1 : ℤ) + 1)
                - ((n : ℤ)^2 - (n : ℤ) + 1) + 2
                = ((n + 2 : ℤ))^2 - (n + 2 : ℤ) + 1 := by
          ring
        simpa [hpoly] using recZ'

      have hle' : n + 2 ≤ (n + 2) ^ 2 := by
        have h1 : 1 ≤ n + 2 := Nat.succ_le_succ (Nat.zero_le (n + 1))
        calc
          n + 2 = (n + 2) * 1 := by simp
          _ ≤ (n + 2) * (n + 2) := Nat.mul_le_mul_left (n + 2) h1
          _ = (n + 2) ^ 2 := by simp [pow_two]
      have cast_sub : (((n + 2) ^ 2 - (n + 2) : ℕ) : ℤ)
              = ((n + 2 : ℤ)) ^ 2 - (n + 2 : ℤ) := by
        simpa [Nat.cast_pow] using (Nat.cast_sub (R := ℤ) hle')
      have rhs_cast : ((n + 2 : ℤ)) ^ 2 - (n + 2 : ℤ) + 1
              = (((n + 2) ^ 2 - (n + 2) + 1 : ℕ) : ℤ) := by
        simp [Nat.cast_add, Nat.cast_one, cast_sub]
      have : f (n + 2) = (n + 2) ^ 2 - (n + 2) + 1 := by
        apply Int.ofNat.inj
        simpa [rhs_cast] using eqZ
      exact this


/-
 My checks
-/
#eval SumOdd 5
#eval (5 : ℕ)^2
#eval (3)!    -- even?
#eval (4)!    -- even
#eval decide (3 ^ 10 > 10 ^ 2)
#eval (g 15, Nat.log 2 15 + 1)
#eval f 5


-- Problem 1: compare SumOdd n and n^2 over a range
#eval List.map SumOdd [0,1,2,3,4,5,6]
#eval List.map (fun n : ℕ => n^2) [0,1,2,3,4,5,6]

-- Problem 2: factorial values and parity for n = 0..7
#eval List.map (fun n => (n, factorial n, (factorial n) % 2)) (List.range 8)

-- Problem 3: values and comparison for a few n
#eval List.map (fun n : ℕ => (n, 3 ^ n, n ^ 2, decide (3 ^ n > n ^ 2))) [1,2,3,4,5,6,7,8,10]

-- Problem 4: g n vs log bound for several n
#eval List.map (fun n : ℕ => (n, g n, Nat.log 2 n + 1, decide (g n ≤ Nat.log 2 n + 1))) [0,1,2,3,4,7,8,15,16,31,32,100]

-- Problem 5: compare f n with n^2 - n + 1 for some n
#eval List.map (fun n : ℕ => (n, f n, n^2 - n + 1, decide (f n = n^2 - n + 1))) [0,1,2,3,4,5,6,10]
