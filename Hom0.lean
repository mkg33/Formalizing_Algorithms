section Logic

variable (P Q R : Prop)

-- Question 1: Fill-in-the-blank proof
-- Hint: Break down the compound implication step by step. You'll need to assume the conjunction,
-- then a premise P, and show how to get to R by going through Q as an intermediate step.
theorem Q1 : (P → Q) ∧ (Q → R) → (P → R) := by
intro h
intro hP
exact (h.2) ((h.1) hP)

-- Question 2: Prove a logical equivalence
-- Hint: Split the biconditional into two directions.
theorem Q2 : P → (Q → R) ↔ (P ∧ Q) → R := by
constructor
· intro h
intro hPQ
obtain ⟨hP, hQ⟩ := hPQ
exact h hP hQ
· intro h
intro hP
intro hQ
exact h ⟨hP, hQ⟩

-- Question 3: Transitivity of divisibility
-- Hint: You can might need follow theorem:
#check Nat.dvd_trans
theorem Q3 (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
exact Nat.dvd_trans h1 h2

-- Question 4: Proving Even Numbers
def even_number (n : ℕ) : Prop := ∃ k, n = 2 * k
theorem Q4 : even_number 4 ∧ even_number 6 := by
constructor
· exact ⟨2, rfl⟩
· exact ⟨3, rfl⟩

-- Question 5: Some divisibility problem
-- The following lemma has partial proof on it. Fill in the sorry to finish the proof.
-- You may find these theorems helpful
#check Dvd.dvd.mul_left
#check Nat.dvd_add_right

-- 'have' tactics is basically a sub-claim that to be filled by the proof.
-- In this problem, you are asked to prove the subclaims and then finish the proof.

lemma Q5 (n k : ℕ) (h1 : k ∣ 21 * n + 4) (h2 : k ∣ 14 * n + 3) : k ∣ 1 := by
have h3 : k ∣ 2 * (21 * n + 4) := by
obtain ⟨m, hm⟩ := h1
use 2 * m
calc
2 * (21 * n + 4)
= 2 * (k * m) := by
rw [hm]
_ = (k * m) * 2 := by
rw [Nat.mul_comm]
_ = k * (m * 2) := by
rw [Nat.mul_assoc]
_ = k * (2 * m) := by
rw [Nat.mul_comm m 2]
have h4 : k ∣ 3 * (14 * n + 3) := by
obtain ⟨m, hm⟩ := h2
use 3 * m
calc
3 * (14 * n + 3)
= 3 * (k * m) := by
rw [hm]
_ = (k * m) * 3 := by
rw [Nat.mul_comm]
_ = k * (m * 3) := by
rw [Nat.mul_assoc]
_ = k * (3 * m) := by
rw [Nat.mul_comm m 3]
have h5 : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1 := by
have h7 : 3 * (14 * n + 3) = 3 * (14 * n) + 3 * 3 := by
rw [Nat.mul_add]
have h8 : 2 * (21 * n + 4) = 2 * (21 * n) + 2 * 4 := by
rw [Nat.mul_add]
rw [h7, h8, Nat.add_assoc, ← Nat.mul_assoc 3 14 n, ← Nat.mul_assoc 2 21 n]
-- Hint: Nat.dvd_add_right is helpful here
-- From h4 and h5, k ∣ 2 * (21 * n + 4) + 1
have h6 : k ∣ 2 * (21 * n + 4) + 1 := by
-- rewrite h4 using h5
have := h4
rw [h5] at this
exact this
have : k ∣ 1 := by
have := (Nat.dvd_add_right h3).1 h6
exact this
exact this