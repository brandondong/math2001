/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 1

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-1,
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  have hq : q = 3 := by addarith [h2]
  rw [hq] at h1
  clear hq h2 q
  addarith [h1]


@[autograded 5]
theorem problem2 {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  have hb : b = a - 1 := by addarith [h2]
  rw [hb] at h1
  clear hb h2 b
  have temp : a + 2 * (a - 1) = 3 * a - 2 := by ring
  rw [temp] at h1
  clear temp
  have h : 3 * a = 3 * 2 := by addarith [h1]
  cancel 3 at h


@[autograded 5]
theorem problem3 {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x * x ^ 2 - 8 * x ^ 2 + 2 * x := by ring
    _ ≥ 9 * x ^ 2 - 8 * x ^ 2 + 2 * 9 := by rel [hx]
    _ = x ^ 2 + 18 := by ring
    _ ≥ 18 := by extra
    _ ≥ 3 := by numbers


@[autograded 5]
theorem problem4 {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  calc
    x ^ 2 - 2 * x = (x - 1) ^ 2 - 1 := by ring
    _ ≥ -1 := by extra


@[autograded 5]
theorem problem5 (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  apply sq_le_sq'
  . assumption
  . assumption
