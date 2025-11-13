import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- # Problem 1: Finding Min Recursively
def minimum (a b : ℕ) : ℕ := if a < b then a else b

-- Consider the following FindMin function
def FindMin (l : List ℕ) : ℕ :=
  match h : l with
  | [] => 0   -- Base case for empty list (0 is minimum in ℕ)
  | x :: xs =>
      if he : xs = [] then x
      else
        have : 1 < l.length := by
          simp [h]
          by_contra!
          observe : xs.length = 0
          simp_all only [le_refl, List.length_eq_zero_iff]
        let n := l.length
        let left := l.take (n / 2)
        let right := l.drop (n / 2)
        minimum (FindMin left) (FindMin right)
termination_by l.length decreasing_by all_goals grind


def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- You can use the following APIs.
-- # In this problem, prove that the FindMin algorithm correctly returns the minimum element for any non-empty input list of size n.
-- You may find the following theorems useful
theorem x_minlist_of_x_lt_minlist {x y : ℕ} {l : List ℕ}
  (h1 : x ≤ y) (h2 : y.MinOfList l) : x.MinOfList l := by
  intro z hz; exact le_trans h1 (h2 z hz)

theorem min_list_of_left_right {x : ℕ} {l : List ℕ} (left right : List ℕ)
  (h_lr : left ++ right = l)
  (h_min_left : x.MinOfList left) (h_min_right : x.MinOfList right) : x.MinOfList l := by
  intro y hy
  have hmem : y ∈ left ++ right := by simpa [h_lr] using hy
  have : y ∈ left ∨ y ∈ right := by simpa [List.mem_append] using hmem
  cases this with
  | inl hl => exact h_min_left _ hl
  | inr hr => exact h_min_right _ hr

-- This is related to my question on Moodle. I proved the membership as well but it doesn't change anything, I guess.
theorem Problem1_strong (l : List ℕ) (h_nonempty : l.length > 0) :
   let z := FindMin l
   z ∈ l ∧ z.MinOfList l := by
  classical
  -- helper for `minimum`
  have minimum_le_left : ∀ a b : ℕ, minimum a b ≤ a := by
    intro a b
    unfold minimum
    by_cases h : a < b
    · simp [h]
    · have hb_le_a : b ≤ a := by
        have : ¬ b > a := by simpa [gt_iff_lt] using h
        exact le_of_not_gt this
      simp [h, hb_le_a]
  have minimum_le_right : ∀ a b : ℕ, minimum a b ≤ b := by
    intro a b
    unfold minimum
    by_cases h : a < b
    · have : a ≤ b := Nat.le_of_lt h
      simp [h, this]
    · simp [h]
  have minimum_eq_left_of_lt : ∀ a b : ℕ, a < b → minimum a b = a := by
    intro a b h; simp [minimum, h]
  have minimum_eq_right_of_not_lt : ∀ a b : ℕ, ¬ a < b → minimum a b = b := by
    intro a b h; simp [minimum, h]
  let Spec : List ℕ → Prop :=
    fun t => (t = [] ∨ FindMin t ∈ t) ∧ (FindMin t).MinOfList t
  -- strong ind on an upper bound for the len of `t`
  have aux : ∀ n (t : List ℕ), t.length ≤ n → Spec t := by
    intro n
    refine Nat.rec (motive := fun n => ∀ t : List ℕ, t.length ≤ n → Spec t) ?base ?step n
    · intro t ht
      cases t with
      | nil =>
          refine ⟨Or.inl rfl, ?_⟩
          simp [FindMin, Nat.MinOfList]
      | cons a s =>
          have : False := by
            have hlen : 1 ≤ (a :: s).length := by simp
            exact Nat.not_succ_le_zero _ (le_trans hlen ht)
          exact this.elim
    · intro n ih t ht
      cases t with
      | nil =>
          refine ⟨Or.inl rfl, ?_⟩
          simp [FindMin, Nat.MinOfList]
      | cons a s =>
          by_cases hs : s = []
          · subst hs
            refine ⟨Or.inr ?_, ?_⟩
            · simp [FindMin]
            · simp [FindMin, Nat.MinOfList]
          ·
            set m := (a :: s).length with hm
            set left := (a :: s).take (m / 2) with hleft
            set right := (a :: s).drop (m / 2) with hright
            have hsplit : left ++ right = a :: s := by
              simp [left, right, List.take_append_drop]
            have hm_pos : 0 < m := by
              dsimp [m]
              exact Nat.succ_pos _
            have hs_pos : 0 < s.length := by
              have : s ≠ [] := by
                simpa [List.length_eq_zero_iff] using hs
              exact List.length_pos_of_ne_nil this
            have htwo_le_m : 2 ≤ m := by
              dsimp [m]
              exact Nat.succ_le_succ (Nat.succ_le_of_lt hs_pos)
            have hdiv_lt : m / 2 < m := Nat.div_lt_self hm_pos (by decide)
            have hdiv_pos : 0 < m / 2 := Nat.div_pos htwo_le_m (by decide)
            have hleft_len : left.length = m / 2 := by
              have : min (m / 2) m = m / 2 := Nat.min_eq_left (Nat.div_le_self _ _)
              simpa [left, m, List.length_take, this]
            have hright_len : right.length = m - m / 2 := by
              simp [right, m, List.length_drop]
            have hleft_lt_m : left.length < m := by
              simpa [hleft_len] using hdiv_lt
            have hleft_pos : 0 < left.length := by
              simpa [hleft_len] using hdiv_pos
            have hleft_ne_nil : left ≠ [] := List.ne_nil_of_length_pos hleft_pos
            have hright_pos : 0 < right.length := by
              have : 0 < m - m / 2 := Nat.sub_pos_of_lt hdiv_lt
              simpa [hright_len] using this
            have hright_ne_nil : right ≠ [] := List.ne_nil_of_length_pos hright_pos
            have hm_le_succ : m ≤ n.succ := by
              dsimp [m]
              exact ht
            have hm_pred_eq : (m - 1).succ = m := Nat.succ_pred_eq_of_pos hm_pos
            have hm_pred_le : m - 1 ≤ n := by
              have : (m - 1).succ ≤ n.succ := by
                simpa [hm_pred_eq] using hm_le_succ
              exact (Nat.succ_le_succ_iff).1 this
            have hone_le_div : 1 ≤ m / 2 := Nat.succ_le_of_lt hdiv_pos
            have hm_sub_le : m - m / 2 ≤ m - 1 := by
              have := Nat.sub_le_sub_left hone_le_div m
              simpa using this
            have hleft_le_n : left.length ≤ n := by
              have hlt : left.length < n.succ := lt_of_lt_of_le hleft_lt_m hm_le_succ
              exact (Nat.lt_succ_iff).1 hlt
            have hright_le_n : right.length ≤ n := by
              have hright_le_pred : right.length ≤ m - 1 := by
                simpa [hright_len] using hm_sub_le
              exact le_trans hright_le_pred hm_pred_le
            have hleft_spec := ih left hleft_le_n
            have hright_spec := ih right hright_le_n
            rcases hleft_spec with ⟨hle_mem_or_nil, hle_min⟩
            rcases hright_spec with ⟨hr_mem_or_nil, hr_min⟩
            have hleft_mem : FindMin left ∈ left := by
              cases hle_mem_or_nil with
              | inl hnil =>
                  exact (hleft_ne_nil hnil).elim
              | inr hmem => exact hmem
            have hright_mem : FindMin right ∈ right := by
              cases hr_mem_or_nil with
              | inl hnil =>
                  exact (hright_ne_nil hnil).elim
              | inr hmem => exact hmem
            have hleft_mem_as : FindMin left ∈ a :: s := by
              have hleft_mem_take : FindMin ((a :: s).take (m / 2)) ∈ (a :: s).take (m / 2) := by
                simpa [hleft] using hleft_mem
              have : FindMin ((a :: s).take (m / 2)) ∈ a :: s :=
                List.mem_of_mem_take hleft_mem_take
              simpa [hleft] using this
            have hright_mem_as : FindMin right ∈ a :: s := by
              have hright_mem_drop : FindMin ((a :: s).drop (m / 2)) ∈ (a :: s).drop (m / 2) := by
                simpa [hright] using hright_mem
              have : FindMin ((a :: s).drop (m / 2)) ∈ a :: s :=
                List.mem_of_mem_drop hright_mem_drop
              simpa [hright] using this
            have hL : minimum (FindMin left) (FindMin right) ≤ FindMin left :=
              minimum_le_left _ _
            have hR : minimum (FindMin left) (FindMin right) ≤ FindMin right :=
              minimum_le_right _ _
            have hmin_left : (minimum (FindMin left) (FindMin right)).MinOfList left :=
              x_minlist_of_x_lt_minlist hL hle_min
            have hmin_right : (minimum (FindMin left) (FindMin right)).MinOfList right :=
              x_minlist_of_x_lt_minlist hR hr_min
            have hmin_total : (minimum (FindMin left) (FindMin right)).MinOfList (a :: s) :=
              min_list_of_left_right left right hsplit hmin_left hmin_right
            have hmem_total : minimum (FindMin left) (FindMin right) ∈ a :: s := by
              by_cases hcmp : FindMin left < FindMin right
              ·
                have hmin_eq : minimum (FindMin left) (FindMin right) = FindMin left :=
                  minimum_eq_left_of_lt _ _ hcmp
                exact hmin_eq.symm ▸ hleft_mem_as
              ·
                have hmin_eq : minimum (FindMin left) (FindMin right) = FindMin right :=
                  minimum_eq_right_of_not_lt _ _ hcmp
                exact hmin_eq.symm ▸ hright_mem_as
            have hfind_eq : FindMin (a :: s) = minimum (FindMin left) (FindMin right) := by
              simp [FindMin, hs, m, left, right]
            have hmem_total' : FindMin (a :: s) ∈ a :: s := by
              simpa [hfind_eq] using hmem_total
            have hmin_total' : (FindMin (a :: s)).MinOfList (a :: s) := by
              simpa [hfind_eq] using hmin_total
            exact ⟨Or.inr hmem_total', hmin_total'⟩
  have hspec := aux l.length l le_rfl
  rcases hspec with ⟨hmem_or_nil, hmin⟩
  have hne : l ≠ [] := List.ne_nil_of_length_pos h_nonempty
  have hmem : FindMin l ∈ l := by
    cases hmem_or_nil with
    | inl hnil => exact (hne hnil).elim
    | inr hmem' => exact hmem'
  exact ⟨hmem, hmin⟩

theorem Problem1 (l : List ℕ) (h_nonempty : l.length > 0) :
    let z := FindMin l
    z.MinOfList l := by
  simpa using (Problem1_strong l h_nonempty).2
