import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- # Problem 3: Implement this function

def safeDivide (x y : ℕ) : Option ℕ :=
  if y = 0 then none else some (x / y)

/-
Implement a function that computes: ((a * b) / c) - ((d * e) / f)

Requirements:
1. Multiply a * b, then divide by c (use safeDivide)
2. Multiply d * e, then divide by f (use safeDivide)
3. Subtract the second result from the first
4. Return none if any division fails or if subtraction would be negative

You'll need this helper:
-/
def safeSub (x y : ℕ) : Option ℕ :=
  if x >= y then some (x - y) else none

/-
Part A: Implement using do notation
-/

def Problem3A (a b c d e f : ℕ) : Option ℕ := do
  let x ← safeDivide (a * b) c
  let y ← safeDivide (d * e) f
  safeSub x y

/-
Part B: Implement the SAME function WITHOUT do notation
(translate your do notation to explicit >>= operator:)
-/

def Problem3B (a b c d e f : ℕ) : Option ℕ :=
  safeDivide (a * b) c >>= fun (x : ℕ) =>
  safeDivide (d * e) f >>= fun (y : ℕ) =>
  safeSub x y
