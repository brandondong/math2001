/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init

/-! # Homework 5

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-5,
for clearer statements and any special instructions. -/

@[autograded 2]
theorem problem1 : ∃ k : ℤ, k > 10 ∧ 3 * k ≡ 2 [ZMOD 5] ∧ k ∣ 72 := by
  use 24
  constructor
  . numbers
  constructor
  . use 14
    ring
  use 3
  ring


@[autograded 3]
theorem problem2 {a : ℤ} (ha : a ≡ 4 [ZMOD 5]) :
    a ^ 3 + 2 * a ^ 2 + 3 ≡ 4 [ZMOD 5] := by
  calc
    a ^ 3 + 2 * a ^ 2 + 3 ≡ 4 ^ 3 + 2 * 4 ^ 2 + 3 [ZMOD 5] := by rel [ha]
    _ = 4 + 5 * 19 := by ring
    _ ≡ 4 [ZMOD 5] := by extra


@[autograded 5]
theorem problem3 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases x % 5
  . calc
      x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [H]
      _ = 0 := by ring
      _ ≡ x [ZMOD 5] := by rel [H]
  . calc
      x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [H]
      _ = 1 := by ring
      _ ≡ x [ZMOD 5] := by rel [H]
  . calc
      x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [H]
      _ = 2 + 5 * 6 := by ring
      _ ≡ 2 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [H]
  . calc
      x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [H]
      _ = 3 + 5 * 48 := by ring
      _ ≡ 3 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [H]
  . calc
      x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [H]
      _ = 4 + 5 * 204 := by ring
      _ ≡ 4 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [H]


@[autograded 3]
theorem problem4 {a : ℚ} (h : ∀ b : ℚ, a + b ^ 2 ≥ 0) : a ≥ 0 := by
  have h2 := h 0
  addarith [h2]


@[autograded 5]
theorem problem5 (n : ℕ) (h : ∀ a : ℕ, 6 ≤ a → a ≤ 10 → a ∣ n) :
    ∀ b : ℕ, 1 ≤ b → b ≤ 5 → b ∣ n := by
  intro b hb1 hb2
  interval_cases b <;> clear hb1 hb2
  . use n
    ring
  . have h2 : 8 ∣ n
    . apply h
      numbers
      numbers
    cases' h2 with x hx
    rw [hx]
    use 4 * x
    ring
  . have h2 : 6 ∣ n
    . apply h
      numbers
      numbers
    cases' h2 with x hx
    rw [hx]
    use 2 * x
    ring
  . have h2 : 8 ∣ n
    . apply h
      numbers
      numbers
    cases' h2 with x hx
    rw [hx]
    use 2 * x
    ring
  . have h2 : 10 ∣ n
    . apply h
      numbers
      numbers
    cases' h2 with x hx
    rw [hx]
    use 2 * x
    ring


@[autograded 3]
theorem problem6 : ∃ a : ℝ, ∀ b : ℝ, a ≤ b ^ 2 := by
  use 0
  intro b
  extra


@[autograded 4]
theorem problem7 : forall_sufficiently_large x : ℝ, x ^ 3 - 5 * x ≥ 11 * x ^ 2 := by
  dsimp
  use 15
  intro x hx
  calc
    x ^ 3 - 5 * x = x * x ^ 2 - 5 * x := by ring
    _ ≥ 15 * x ^ 2 - 5 * x := by rel [hx]
    _ = 11 * x ^ 2 + 4 * x * x - 5 * x := by ring
    _ ≥ 11 * x ^ 2 + 4 * 15 * x - 5 * x := by rel [hx]
    _ = 11 * x ^ 2 + 55 * x := by ring
    _ ≥ 11 * x ^ 2 := by extra
