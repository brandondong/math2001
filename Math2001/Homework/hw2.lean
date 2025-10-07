/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 2

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-2,
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 {x : ℚ} (h1 : x ^ 2 = 9) (h2 : 1 < x) : x = 3 := by
  have h : x ^ 2 - 9 = 0 := by addarith [h1]
  have h3 : (x + 3) * (x - 3) = 0
  . calc
      (x + 3) * (x - 3) = x ^ 2 - 9 := by ring
      _ = 0 := h
  clear h h1
  have H := eq_zero_or_eq_zero_of_mul_eq_zero h3
  cases' H with H H
  . have contra := calc
      1 < x := h2
      _ = x + 3 - 3 := by ring
      _ = 0 - 3 := by rw [H]
    numbers at contra
  . addarith [H]


@[autograded 5]
theorem problem2 {s : ℚ} (h1 : 3 * s ≤ -15) (h2 : 2 * s ≥ -10) : s = -5 := by
  have h : 3 * s ≤ 3 * -5 := by addarith [h1]
  cancel 3 at h
  have h4 : 2 * s ≥ 2 * -5 := by addarith [h2]
  cancel 2 at h4
  clear h1 h2
  exact Rat.le_antisymm h h4


@[autograded 4]
theorem problem3 {t : ℚ} (h : t = 2 ∨ t = -3) : t ^ 2 + t - 6 = 0 := by
  cases' h with h h <;> rw [h] <;> ring


@[autograded 5]
theorem problem4 {x : ℤ} : 3 * x ≠ 10 := by
  have h : ¬(3: ℤ) ∣ 10
  . apply Int.not_dvd_of_exists_lt_and_lt
    use 3
    constructor <;> numbers
  intro h2
  apply h
  use x
  rw [h2]


@[autograded 6]
theorem problem5 {x y : ℝ} (h1 : 2 ≤ x ∨ 2 ≤ y) (h2 : x ^ 2 + y ^ 2 = 4) :
    x ^ 2 * y ^ 2 = 0 := by
  cases' h1 with h h
  . have goal : y = 0
    . have sub : x = 2
      . cases' lt_or_eq_of_le h with h3 h3
        . have contra := calc
            4 = x ^ 2 + y ^ 2 := by rw [h2]
            _ > 2 ^ 2 + y ^ 2 := by rel [h3]
            _ ≥ 2 ^2 := by extra
          numbers at contra
        rw [h3]
      rw [sub] at h2
      clear sub h x
      have h : y ^ 2 = 0 := by addarith [h2]
      have temp : y ^ 2 = y * y := by ring
      rw [temp] at h
      clear temp h2
      have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
      cases' h2 with h2 h2 <;> assumption
    rw [goal]
    ring
  . have goal : x = 0
    . have sub : y = 2
      . cases' lt_or_eq_of_le h with h3 h3
        . have contra := calc
            4 = x ^ 2 + y ^ 2 := by rw [h2]
            _ > x ^ 2 + 2 ^ 2 := by rel [h3]
            _ ≥ 2 ^2 := by extra
          numbers at contra
        rw [h3]
      rw [sub] at h2
      clear sub h y
      have h : x ^ 2 = 0 := by addarith [h2]
      have temp : x ^ 2 = x * x := by ring
      rw [temp] at h
      clear temp h2
      have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
      cases' h2 with h2 h2 <;> assumption
    rw [goal]
    ring
