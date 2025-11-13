import Mathlib.Tactic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option tactic.hygienic false


section
open Set
variable {α : Type*}
variable (A B C : Set α)

/-
Strategy for P1: we show both directions by reasoning on set elements. In more concrete terms:

(->) We assume h : (B ∪ C) ⊆ A. To show B ⊆ A, it's enough to take an arbitrary x with x ∈ B. It then follows that x ∈ B ∪ C by the left injection, and so x ∈ A by h. An analogous argument with the right injection gives us C ⊆ A.
(<-) We now assume hB : B ⊆ A and hC : C ⊆ A. Let x ∈ B ∪ C. We then have: x ∈ B ∨ x ∈ C. In the 'left' case, we obtain x ∈ A by hB. Similarly, in the 'right' case, we get x ∈ A by hC. And so: (B ∪ C) ⊆ A. In the proof, we just use union injections, and reasoning by case analysis on situation where x ∈ B ∪ C. We also apply the definition of ⊆ multiple times.
-/
lemma P1 : (B ∪ C) ⊆ A ↔ B ⊆ A ∧ C ⊆ A := by
  constructor
  · intro h
    constructor
    · intro x hxB
      apply h
      left
      exact hxB
    · intro x hxC
      apply h
      right
      exact hxC
  · intro h
    cases h with
    | intro hB hC =>
      intro x hx
      rw [mem_union] at hx
      cases hx with
      | inl hxB => exact hB hxB
      | inr hxC => exact hC hxC

/-
Strategy for P2: we apply set extensionality, that is, we fix an arbitrary x and prove two implications of set memberships. In more concrete terms:

(->) The case x ∈ A ∩ (B ∪ C) means that (x ∈ A) ∧ (x ∈ B ∨ x ∈ C). We now apply the distribution of ∧ over ∨ to get (x ∈ A ∧ x ∈ B) ∨ (x ∈ A ∧ x ∈ C). In the Lean proof, this means that we have to unpack and do a case on disjunction. This is precisely: x ∈ (A ∩ B) ∪ (A ∩ C).
(<-) We now consider this case: x ∈ (A ∩ B) ∪ (A ∩ C). It follows that either x ∈ A ∩ B or x ∈ A ∩ C. In the first case, it holds that x ∈ A and x ∈ B, and so x ∈ B ∪ C, hence x ∈ A ∩ (B ∪ C). The second case is completely analogous.
-/
theorem P2 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | intro hA hBC =>
      rw [mem_union] at hBC
      cases hBC with
      | inl hB =>
        left
        exact And.intro hA hB
      | inr hC =>
        right
        exact And.intro hA hC
  · intro hx
    rw [mem_union] at hx
    cases hx with
    | inl hAB =>
      cases hAB with
      | intro hA hB =>
        constructor
        · exact hA
        · left; exact hB
    | inr hAC =>
      cases hAC with
      | intro hA hC =>
        constructor
        · exact hA
        · right; exact hC

/-
Strategy for P3: We again apply extensionality and an additional case on whether x ∈ A.

(->) Let us assume x ∈ (A ∪ B), x ∈ (A ∪ C), and x ∈ (B ∪ C). We consider two cases as follows:
a) If x ∈ A, then from x ∈ B ∪ C we get x ∈ B ∨ x ∈ C, and so x ∈ A ∩ B in the first sub-case and also x ∈ A ∩ C in the second sub-case. This implies that x lies in the set on the right-hand side.
b) Now, if x ∉ A, then x ∈ A ∪ B implies x ∈ B, and x ∈ A ∪ C implies x ∈ C, and so: x ∈ B ∩ C, which means that x lies in the right-hand side. In the Lean proof, we use classical decidability for membership in this split.
(<-) We split on the right-hand side:
a) From x ∈ A ∩ B, we inject x into A ∪ B and A ∪ C via A, and into B ∪ C via B.
b) From x ∈ A ∩ C, we inject analogously via A and C.
c) From x ∈ B ∩ C, we inject into A ∪ B via B, into A ∪ C via C, and also into B ∪ C.
This implies that x lies in the left-hand side.
-/
theorem P3 : (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | intro hx12 hx3 =>
      cases hx12 with
      | intro hx1 hx2 =>
        rw [mem_union] at hx1
        rw [mem_union] at hx2
        rw [mem_union] at hx3
        -- extra justification for using `classical`:
        -- `by_cases hA : x ∈ A` requires `[Decidable (x ∈ A)]`.
        -- for an arbitrary `Set α`, we have no such instance.
        -- `classical` ensures propositional decidability (`propDecidable`).
        classical
        by_cases hA : x ∈ A
        · cases hx3 with
          | inl hB =>
            left; left
            exact And.intro hA hB
          | inr hC =>
            left; right
            exact And.intro hA hC
        · cases hx1 with
          | inl hA1 =>
            contradiction
          | inr hB =>
            cases hx2 with
            | inl hA2 =>
              contradiction
            | inr hC =>
              right
              exact And.intro hB hC
  · intro hx
    rw [mem_union] at hx
    cases hx with
    | inl hABorAC =>
      rw [mem_union] at hABorAC
      cases hABorAC with
      | inl hAB =>
        cases hAB with
        | intro hA hB =>
          constructor
          · constructor
            · left; exact hA
            · left; exact hA
          · left; exact hB
      | inr hAC =>
        cases hAC with
        | intro hA hC =>
          constructor
          · constructor
            · left; exact hA
            · left; exact hA
          · right; exact hC
    | inr hBC =>
      cases hBC with
      | intro hB hC =>
        constructor
        · constructor
          · right; exact hB
          · right; exact hC
        · left; exact hB

-- The set difference operation is denoted by B \ A
#check mem_diff
#check subset_union_left

/-
Strategy for P4: we apply the monotonicity of union with an explicit witness X := B \ A. In more precise terms:

(->) If A ∪ X = B, then A ⊆ A ∪ X by left inclusion. We may rewrite the codomain with the equality and we then obtain A ⊆ B.
(<-) We now assume h : A ⊆ B and set X := B \ A. We prove A ∪ X = B by mutual inclusion.
a) ⊆: If x ∈ A, then h gives x ∈ B. If x ∈ B \ A, then we have x ∈ B (simply by the definition of a difference).
b) ⊇: If x ∈ B and x ∈ A, then x ∈ A ∪ X by left injection. Now, if x ∈ B and x ∉ A, then x ∈ B \ A (by definition). It follows that x ∈ A ∪ X by right injection. In our Lean proof, we again use classical decidability for the split on x ∈ A.
-/
theorem P4 : (∃ X : Set α, A ∪ X = B) ↔ A ⊆ B := by
  constructor
  · intro h
    cases h with
    | intro X hX =>
      -- goal: A ⊆ B
      rw [← hX]
      apply subset_union_left
  · intro h
    apply Exists.intro (B \ A)
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hxA =>
        exact h hxA
      | inr hxBA =>
        rw [mem_diff] at hxBA
        cases hxBA with
        | intro hxB hxNotA => exact hxB
    · intro hxB
      -- extra justification for `classical`:
      -- we split cases on `x ∈ A`, and this requires `[Decidable (x ∈ A)]`.
      -- `classical` ensures decidability.
      classical
      by_cases hxA : x ∈ A
      · left; exact hxA
      · right
        rw [mem_diff]
        constructor
        · exact hxB
        · exact hxA
end

section
variable {α : Type*} [DecidableEq α]
variable (A B C : Finset α)

open Finset

/- Recall:
  rw [thm] replaces a with b in an equality a = b.
  rw [← thm] replaces b with a.
-/

def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k
def IsDisjoint (A B: Finset α) : Prop := A ∩ B = ∅

#check card_union
#check card_eq_zero
#check Nat.two_mul

/-
Strategy for P5: The main idea is to reduce to the identity with union cardinality and then rewrite the hypotheses.

Observe that from A ∩ B = ∅ , we obtain #(A ∩ B) = 0 by the (finite-set) equivalence #S = 0 ↔ S = ∅. We now apply inclusion-exclusion for finite unions as follows:
  #(A ∪ B) = #A + #B − #(A ∩ B),
and this simplifies to #(A ∪ B) = #A + #B. We now rewrite with A ∪ B = U to obtain #U = #A + #B, and then with #A = #B to get #U = #B + #B = 2 · #B. We take k := #B as the witness for the even property: #U = 2k.
-/
theorem P5 (U : Finset α) (A B : Finset α)
  (hAB : IsDisjoint A B) (hcard : #A = #B) (htotal : A ∪ B = U) :
  IsEven (#U) := by
  -- #(A ∩ B) = 0 from the hypothesis (disjoint)
  have hAB' : #(A ∩ B) = 0 := by
    apply (Finset.card_eq_zero).2
    exact (hAB : A ∩ B = ∅)
  -- cardinality (union)
  have AB_eq : #(A ∪ B) = #A + #B := by
    have h := card_union (s := A) (t := B)
    rw [hAB', Nat.sub_zero] at h
    exact h
  have hU : #U = #B + #B := by
    have t := AB_eq
    rw [htotal] at t
    rw [hcard] at t
    exact t
  -- witness
  apply Exists.intro (#B)
  rw [Nat.two_mul]
  exact hU
end
