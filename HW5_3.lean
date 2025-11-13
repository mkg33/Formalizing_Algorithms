import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

-- For problem 3 and 4, we will use the following version of Merge and Sorted
-- # Merge
def Merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

-- # Problem 3: Prove that y ∈ Merge xs (y :: ys)
-- You may find this List functions helpful
#check List.mem_cons_of_mem
#check List.mem_cons_self

theorem Problem3 (y : ℕ) (xs ys: List ℕ) : y ∈ Merge xs (y :: ys) := by
  induction xs with
  | nil => simp [Merge]
  | cons x xs ih =>
      by_cases hxy : x ≤ y
      · simp [Merge, hxy, List.mem_cons, ih]
      · simp [Merge, hxy]

