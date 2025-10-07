/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs
import AutograderLib

math2001_init

open Int

/-! # Homework 4

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-4,
for clearer statements and any special instructions. -/

@[autograded 5]
theorem problem1 (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  have h := Int.even_or_odd n
  cases' h with h h <;> cases' h with w hw <;> rw [hw] <;> clear hw n
  . use 6 * w ^ 2 + 3 * w - 1
    ring
  . use 6 * w ^ 2 + 9 * w + 2
    ring


@[autograded 1]
theorem problem2 : (8 : ℤ) ∣ 96 := by
  use 12
  ring


@[autograded 2]
theorem problem3 : ¬(8 : ℤ) ∣ -55 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -7
  constructor <;> numbers


@[autograded 4]
theorem problem4 {a b c : ℤ} (hab : a ^ 3 ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 6 ∣ c := by
  cases' hab with x hx
  cases' hbc with y hy
  rw [hy]
  rw [hx]
  clear hx hy c b
  use x ^ 2 * y
  ring


@[autograded 1]
theorem problem5 : 31 ≡ 13 [ZMOD 3] := by
  use 6
  ring


@[autograded 2]
theorem problem6 : ¬ 51 ≡ 62 [ZMOD 5] := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -3
  constructor <;> numbers


@[autograded 5]
theorem problem7 (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  cases' h with x hx
  use x * (a ^ 2 + a * b + b ^ 2)
  have temp : n * (x * (a ^ 2 + a * b + b ^ 2)) = (n * x) * (a ^ 2 + a * b + b ^ 2) := by ring
  rw [temp]
  rw [← hx]
  ring


@[autograded 5]
theorem problem8 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  cases' h1 with x hx
  cases' h2 with y hy
  use (x + y)
  calc
    a - c = a - b + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
  ring
