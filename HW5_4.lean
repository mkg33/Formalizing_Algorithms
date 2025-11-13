import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

-- For problem 3 and 4, we will use the following version of Merge and Sorted
-- # Merge
def Merge : List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x :: xs, y :: ys =>
      if x ≤ y then x :: Merge xs (y :: ys)
      else y :: Merge (x :: xs) ys

def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- # Sorted
inductive Sorted : List ℕ → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a : ℕ) (t : List ℕ) : a.MinOfList t → Sorted t → Sorted (a :: t)

@[simp] theorem merge_nil_left (xs : List ℕ) : Merge [] xs = xs := by
  cases xs with
  | nil =>
      unfold Merge
      simp
  | cons _ _ =>
      unfold Merge
      simp

@[simp] theorem merge_nil_right (xs : List ℕ) : Merge xs [] = xs := by
  cases xs with
  | nil =>
      unfold Merge
      simp
  | cons _ _ =>
      unfold Merge
      simp

theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by
  cases hxs with
  | cons _ _ _ _ hst => exact hst
  | cons_min _ _ _ hst => exact hst
  | single _ => exact Sorted.nil

def HeadMinProp : List ℕ → Prop
  | [] => True
  | x :: xs => x.MinOfList xs

theorem sorted_head_min : ∀ {l : List ℕ}, Sorted l → HeadMinProp l := by
  intro l h
  induction h with
  | nil =>
      simp [HeadMinProp]
  | single a =>
      simp [HeadMinProp, Nat.MinOfList]
  | cons a b t hab hst ih =>
      have hbmin : b.MinOfList t := by
        simpa [HeadMinProp] using ih
      dsimp [HeadMinProp]
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · simpa using hab
      · exact le_trans hab (hbmin _ hy')
  | cons_min a t hmin _ ih =>
      simpa [HeadMinProp] using hmin

theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : x.MinOfList xs := by
  have := sorted_head_min hxs
  simpa [HeadMinProp] using this

theorem merge_min_out (x : ℕ) (xs ys : List ℕ)
    (h_min_in_xs : ∀ y ∈ xs, x ≤ y) : Merge (x :: ys) xs = x :: Merge ys xs := by
  cases xs with
  | nil => simp [merge_nil_right]
  | cons y ys' =>
      have hx : x ≤ y := h_min_in_xs y (by simp)
      simp [Merge, hx]

theorem merge_min_out_sym (x : ℕ) (xs ys : List ℕ)
    (h_min_in_xs : ∀ y ∈ xs, x ≤ y) (h_min_in_ys : ∀ y ∈ ys, x ≤ y) :
    Merge ys (x :: xs) = x :: Merge ys xs := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      have hx_y : x ≤ y := h_min_in_ys y (by simp)
      by_cases hyx : y ≤ x
      · have hxy : x = y := le_antisymm hx_y hyx
        subst hxy
        have hys : ∀ z ∈ ys, x ≤ z := by
          intro z hz; exact h_min_in_ys z (by simp [hz])
        have hrec := ih hys
        simp [Merge, hrec, merge_min_out x xs ys h_min_in_xs]
      ·
        simp [Merge, hyx]

-- # Problem 4: Prove that Merge function is commutative on sorted inputs
-- `nth_rewrite` tactic can be useful to rewrite a specific occurrence
-- You may find this function useful and you may find the API about merge and sorted helpful
#check Merge.eq_def

-- # API about Merge
-- In this homework, let's assume you have access to the following theorems.
-- Proving these theorems are optional.
theorem Problem4 (xs ys : List ℕ) (h1 : Sorted xs) (h2 : Sorted ys) :
    Merge xs ys = Merge ys xs := by
  classical
  have aux :
      ∀ k xs ys,
        xs.length + ys.length = k →
        Sorted xs → Sorted ys →
        Merge xs ys = Merge ys xs := by
    intro k
    refine Nat.rec (motive := fun k => ∀ xs ys,
      xs.length + ys.length = k → Sorted xs → Sorted ys → Merge xs ys = Merge ys xs) ?base ?step k
    · intro xs ys hlen hxs hys
      obtain ⟨hx, hy⟩ := Nat.add_eq_zero.mp hlen
      have hxs_nil : xs = [] := by simpa [List.length_eq_zero_iff] using hx
      have hys_nil : ys = [] := by simpa [List.length_eq_zero_iff] using hy
      subst hxs_nil
      subst hys_nil
      rfl
    · intro k ih xs ys hlen hxs hys
      cases xs with
      | nil => simp
      | cons a as =>
          cases ys with
          | nil => simp
          | cons b bs =>
              have h_as_sorted : Sorted as := sorted_suffix hxs
              have h_bs_sorted : Sorted bs := sorted_suffix hys
              have hmin_a : a.MinOfList as := sorted_min hxs
              have hmin_b : b.MinOfList bs := sorted_min hys
              have hlen_succ : Nat.succ (as.length + bs.length + 1) = Nat.succ k := by
                simpa [List.length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen
              have hlen_tail : as.length + bs.length + 1 = k := Nat.succ.inj hlen_succ
              have hlen_left : as.length + (b :: bs).length = k := by
                simpa [List.length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen_tail
              have hlen_right : (a :: as).length + bs.length = k := by
                simpa [List.length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen_tail
              by_cases hab : a ≤ b
              · have hmin_in_ys : ∀ y ∈ b :: bs, a ≤ y := by
                  intro y hy
                  rcases List.mem_cons.1 hy with hy | hy
                  · simpa [hy] using hab
                  · exact le_trans hab (hmin_b _ hy)
                have hleft : Merge (a :: as) (b :: bs) = a :: Merge as (b :: bs) :=
                  merge_min_out a (b :: bs) as hmin_in_ys
                have hright : Merge (b :: bs) (a :: as) = a :: Merge (b :: bs) as :=
                  merge_min_out_sym a as (b :: bs)
                    (by intro y hy; exact hmin_a _ hy)
                    hmin_in_ys
                have hswap : Merge as (b :: bs) = Merge (b :: bs) as :=
                  ih as (b :: bs) hlen_left h_as_sorted hys
                have hleft' : Merge (a :: as) (b :: bs) = a :: Merge (b :: bs) as :=
                  hleft.trans (congrArg (List.cons a) hswap)
                have hright' : Merge (b :: bs) (a :: as) = a :: Merge (b :: bs) as := hright
                exact hleft'.trans hright'.symm
              · have hba : b ≤ a := le_of_not_ge hab
                have hswap : Merge (a :: as) bs = Merge bs (a :: as) :=
                  ih (a :: as) bs hlen_right hxs h_bs_sorted
                simp [Merge, hab, hba, hswap]
  simpa using aux (xs.length + ys.length) xs ys rfl h1 h2
