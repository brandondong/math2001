/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import AutograderLib

math2001_init

open Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/

@[autograded 2]
theorem problem1 {a b : ℚ} (h : a = 3 - b) : a + b = 3 ∨ a + b = 4 := by
  left
  addarith [h]


@[autograded 5]
theorem problem2 {t : ℚ} (h : t ^ 2 + t - 6 = 0) : t = 2 ∨ t = -3 := by
  have temp : t ^ 2 + t - 6 = (t - 2) * (t + 3) := by ring
  rw [temp] at h
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
  cases' h2 with h2 h2
  . left
    addarith [h2]
  . right
    addarith [h2]


@[autograded 3]
theorem problem3 : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  use 4, 3
  constructor <;> numbers


@[autograded 5]
theorem problem4 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_lt x 0
  cases' H with h h
  . use 1
    calc
      1 ^ 2 > 0 := by numbers
      _ ≥ x := by rel [h]
  . use x+1
    calc
      (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring
      _ ≥ 2 * x + 1 := by extra
      _ > 2 * x := by extra
      _ = x + x := by ring
      _ ≥ x := by extra


@[autograded 5]
theorem problem5 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  cases' hx with w hw
  rw [hw]
  clear hw x
  use 4 * w ^ 3 + 6 * w ^ 2 + 3 * w
  ring


@[autograded 5]
theorem problem6 (n : ℕ) : ∃ m ≥ n, Odd m := by
  have h := Nat.even_or_odd n
  cases' h with h h
  . cases' h with w hw
    use n + 1
    constructor
    . extra
    use w
    rw [hw]
  . use n
    constructor
    . extra
    apply h
