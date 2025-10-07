/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init


/-! # Homework 7

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-7,
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor <;> intro h
  . push_neg at h
    apply h
  . intro h2
    cases' h with h h3
    apply h3
    apply h2
    apply h


@[autograded 3]
theorem problem2 : ¬ (∀ x : ℚ, 2 * x ^ 2 ≥ x) := by
  push_neg
  use 0.25
  numbers


@[autograded 4]
theorem problem3 (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  sorry

@[autograded 4]
theorem problem4 (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  sorry

@[autograded 5]
theorem problem5 {a : ℝ} (ha : -1 ≤ a) : ¬ ∃ n : ℕ, (1 + a) ^ n < 1 + n * a := by
  push_neg
  intro n
  simple_induction n with k hk
  . conv => ring
  calc
    1 + (k + 1) * a = 1 + k * a + a := by ring
    _ ≤  (1 + a) ^ k + a := by rel [hk]
  have temp : (1 + a) ^ (k + 1) = (1 + a) ^ k + a * (1 + a) ^ k := by ring
  rw [temp]
  clear temp hk
  have goal : a ≤ a * (1 + a) ^ k
  . simple_induction k with x IH
    . conv => ring
    have r1 : (1 + a) ^ x ≥ 0
    . clear IH
      simple_induction x with y IH
      . conv => ring
        numbers
      have temp : 1 + a ≥ 0 := by addarith [ha]
      calc
        (1 + a) ^ (y + 1) = (1 + a) ^ y * (1 + a) := by ring
        _ ≥ 0 * (1 + a) := by rel [IH]
        _ ≥ 0 := by extra
    calc
      a ≤ a * (1 + a) ^ x := IH
      _ ≤ a * (1 + a) ^ x + a ^ 2 * (1 + a) ^ x := by extra
      _ = _ := by ring
  rel [goal]


@[autograded 4]
theorem problem6 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 10
  intro x hx
  induction_from_starting_point x, hx with k hk IH
  . numbers
  calc
    (3:ℤ) ^ (k + 1) = 3 * (3 ^ k) := by ring
    _ ≥ 3 * (2 ^ k + 100) := by rel [IH]
    _ = 2 ^ (k + 1) + 100 + 2 ^ k + 200 := by ring
    _ ≥ 2 ^ (k + 1) + 100 + 2 ^ k := by extra
    _ ≥ 2 ^ (k + 1) + 100 := by extra
