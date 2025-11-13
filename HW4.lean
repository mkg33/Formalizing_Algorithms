import Mathlib.Tactic
set_option autoImplicit false
set_option tactic.hygienic false

open Classical

-- All tactics are welcome.

-- # Problem 1: Predicate AllEven
-- Define Predicate AllEven is true if every number in the list is even.
-- e.g., [], [2], [8, 0, 4]
-- Complete the definition for AllEven. It should take a list of natural numbers (List ℕ) and return a Prop

def isEven (n :ℕ) : Prop := ∃k, n = 2*k

-- Your AllEven must use isEven function above
inductive AllEven : List ℕ → Prop
| nil : AllEven []
| cons {n : ℕ} {l : List ℕ} : isEven n → AllEven l → AllEven (n :: l)

-- Prove that your AllEven predicate is equivalent to checking if every element in the list is even.
-- Let's split into two parts

-- # Part 1
theorem Problem1_1 (l : List ℕ)  :
  AllEven l → ∀ n ∈ l, isEven n := by
  intro h
  induction h with
  | nil =>
    intro n hn
    cases hn
  | @cons a t ha ht ih =>
    intro n hn
    have h' : n = a ∨ n ∈ t := by
      simpa [List.mem_cons] using hn
    cases h' with
    | inl hEq => simpa [hEq] using ha
    | inr hmem => exact ih n hmem

-- # Part 2
theorem Problem1_2 (l : List ℕ)  :
  (h : ∀ n ∈ l, isEven n) → AllEven l := by
  intro h
  induction l with
  | nil =>
    exact AllEven.nil
  | cons a t ih =>
    have ha : isEven a := h a (by simp)
    have ht : ∀ n ∈ t, isEven n := by
      intro n hn
      exact h n (by simp [List.mem_cons, hn])
    exact AllEven.cons ha (ih ht)

-- # Sorted
-- We will use the following version of Sorted

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

inductive Sorted: List ℕ  → Prop
| nil : Sorted []
| single (a : ℕ) : Sorted [a]
| cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
| cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 2: Prove that a list of length at most 1 is sorted.
def len : List ℕ → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

theorem Problem2 (l : List ℕ) (h : len l ≤ 1) : Sorted l := by
  cases l with
  | nil =>
    exact Sorted.nil
  | cons a l1 =>
    cases l1 with
    | nil =>
      exact Sorted.single a
    | cons b t =>
      have hlen : len t + 2 = len (a :: b :: t) := by
        dsimp [len]
        calc
          len t + 2
              = len t + (1 + 1) := by rfl
          _ = (len t + 1) + 1 := by
            simp [Nat.add_assoc]
          _ = (1 + len t) + 1 := by
            rw [Nat.add_comm (len t) 1]
          _ = 1 + (len t + 1) := by
            rw [Nat.add_assoc 1 (len t) 1]
          _ = 1 + (1 + len t) := by
            simp [Nat.add_comm]
          _ = len (a :: b :: t) := by
            simp [len]
      have h2 : 2 ≤ len (a :: b :: t) := by
        have : 2 ≤ len t + 2 := Nat.le_add_left 2 (len t)
        exact hlen ▸ this
      exact False.elim ((Nat.not_succ_le_self 1) (Nat.le_trans h2 h))

-- # Problem 3: Prove basic properties of Sorted
theorem Problem3_1 {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by
  cases hxs with
  | single _ =>
    exact Sorted.nil
  | cons _ _ _ _ hst =>
    exact hst
  | cons_min _ _ _ hst =>
    exact hst

theorem Problem3_2 {x y : ℕ} {t : List ℕ} (hsort : Sorted (x :: y :: t)) : y.MinOfList t := by
  have hyt : Sorted (y :: t) := Problem3_1 hsort
  have headMin : ∀ {l : List ℕ}, Sorted l →
      match l with
      | [] => True
      | y :: t => y.MinOfList t := by
    intro l h
    induction h with
    | nil =>
      exact trivial
    | single a =>
      change a.MinOfList []
      intro z hz
      cases hz
    | cons a b u hle hst ih =>
      change a.MinOfList (b :: u)
      intro z hz
      have hz' : z = b ∨ z ∈ u := by
        simpa [List.mem_cons] using hz
      cases hz' with
      | inl hEq =>
        simpa [hEq] using hle
      | inr hmem =>
        have hbMin : b.MinOfList u := by
          simpa using ih
        have hb : b ≤ z := hbMin z hmem
        exact Nat.le_trans hle hb
    | cons_min a t hmin _ =>
      simpa using hmin
  simpa using headMin (l := y :: t) hyt

-- # Problem 4: Alternate Definitions of Sorted
-- Consider the following inductive predicate
inductive Sorted2: List ℕ  → Prop
| nil : Sorted2 []
| single (a : ℕ) : Sorted2 [a]
| cons (a b : ℕ ) (t : List ℕ ) : a ≤ b → Sorted2 (b :: t) → Sorted2 (a :: b :: t)

-- Prove that Sorted2 is equivalent to Sorted
-- You may find ext tactic useful
theorem Problem4 : Sorted2 = Sorted := by
  funext l
  apply propext
  constructor
  · intro h
    induction h with
    | nil =>
      exact Sorted.nil
    | single a =>
      exact Sorted.single a
    | cons a b t hab hst ih =>
      exact Sorted.cons a b t hab ih
  · intro h
    induction h with
    | nil =>
      exact Sorted2.nil
    | single a =>
      exact Sorted2.single a
    | cons a b t hab hst ih =>
      exact Sorted2.cons a b t hab ih
    | cons_min a t hmin hst ih =>
      cases t with
      | nil =>
        simpa using Sorted2.single a
      | cons b u =>
        have hle : a ≤ b := hmin b (by simp)
        exact Sorted2.cons a b u hle ih

-- # Problem 5: Binary Tree
-- Consider the following version of BinaryTree
inductive BinaryTree
| nil
| node (left : BinaryTree) (key : ℕ) (right : BinaryTree)

-- Define mirror operation as reversing the tree
def mirror : BinaryTree → BinaryTree
| BinaryTree.nil        => BinaryTree.nil
| BinaryTree.node l key r => BinaryTree.node (mirror r) key (mirror l)

-- A binary tree is complete if every node has either two non-empty subtrees or two empty subtrees.
-- We can define it using inductive predicate as follows.

inductive Complete : BinaryTree  → Prop
| leaf : Complete BinaryTree.nil
| node  (l : BinaryTree) (key : ℕ) (r : BinaryTree)
(hl : Complete l) (hr : Complete r)
(hiff : l = BinaryTree.nil ↔ r = BinaryTree.nil) :
Complete (BinaryTree.node l key r)

@[simp] theorem mirror_mirror (t : BinaryTree) : mirror (mirror t) = t := by
induction t with
| nil => simp [mirror]
| node l k r ihl ihr => simp [mirror, ihl, ihr]

@[simp] theorem mirror_eq_nil_iff (t : BinaryTree) :
mirror t = BinaryTree.nil ↔ t = BinaryTree.nil := by
constructor
· intro h
  have : mirror (mirror t) = BinaryTree.nil := by
    simpa [mirror] using congrArg mirror h
  simpa [mirror_mirror] using this
· intro h
  simp [h, mirror]

-- Prove that if a mirror of t is complete then t is complete
theorem Problem5 :
  ∀ t : BinaryTree, Complete (mirror t) → Complete t := by
  intro t
  induction t with
  | nil =>
    intro _
    exact Complete.leaf
  | node l k r ihl ihr =>
    intro h
    have h' : Complete (BinaryTree.node (mirror r) k (mirror l)) := by
      simpa [mirror] using h
    cases h' with
    | node _ _ _ hl hr hiff =>
      have cl : Complete l := ihl hr
      have cr : Complete r := ihr hl
      have hiff' : l = BinaryTree.nil ↔ r = BinaryTree.nil := by
        have : r = BinaryTree.nil ↔ l = BinaryTree.nil := by
          simpa [mirror_eq_nil_iff] using hiff
        simpa [Iff.comm] using this
      exact Complete.node l k r cl cr hiff'