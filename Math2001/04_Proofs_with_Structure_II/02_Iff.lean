/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    cases' h with x hx
    use x
    calc
      n = (n - 1) + 1 := by ring
      _ = 2 * x + 1 := by rw [hx]


theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    cases' h with x hx
    use x
    calc
      n = n - 0 := by ring
      _ = 2 * x := by rw [hx]


example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  intro h
  have h2 := calc
    (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
    _ = 0 := by rw [h]
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  cases' h3 with h3 h3
  left
  addarith [h3]
  right
  addarith [h3]
  intro h
  cases' h with h h
  rw [h]
  ring
  rw [h]
  ring


example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  intro h
  have h1 := calc
    (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
    _ ≤ 4 * -1 + 5 := by rel [h]
    _ = 1 ^ 2 := by ring
  have h1_2 : (0: ℤ) ≤ 1 := by numbers
  have h2 := abs_le_of_sq_le_sq' h1 h1_2
  cases' h2 with h2 h3
  have h4 : 2 * 2 ≤ 2 * a
  addarith [h2]
  cancel 2 at h4
  have h5 : 2 * a ≤ 2 * 3
  addarith [h3]
  cancel 2 at h5
  interval_cases a
  left
  ring
  right
  ring
  intro h
  cases' h with h h
  rw [h]
  numbers
  rw [h]
  numbers


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  cases' hn2 with hn2 hn2
  use 2
  addarith [hn2]
  use 3
  addarith [hn2]


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  cases' hn1 with hn2 hn2
  use 2
  addarith [hn2]
  use 3
  addarith [hn2]


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    assumption


/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  intro h
  have h1 : 2 * x = 2 * 6 := by addarith [h]
  cancel 2 at h1
  intro h
  rw [h]
  ring


example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  intro h
  cases' h with x hx
  rw [hx]
  constructor
  use 9*x
  ring
  use 7*x
  ring
  intro h
  cases' h with h1 h2
  cases' h1 with x hx
  cases' h2 with y hy
  use 4 * y - 3 * x
  calc
    n = 28 * n - 27 * n := by ring
    _ = 28 * (9 * y) - 27 * n := by rw [hy]
    _ = 28 * (9 * y) - 27 * (7 * x) := by rw [hx]
    _ = _ := by ring


theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  intro h
  cases' h with x hx
  use x
  addarith [hx]
  intro h
  cases' h with x hx
  use x
  addarith [hx]


example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [dvd_iff_modEq] at *
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b ≡ 2 * 0 ^ 3 - 0 ^ 2 + 3 * 0 [ZMOD a] := by rel [hab]
    _ = 0 := by ring


example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  intro h
  have h1 : k ^ 2 < 3 ^ 2
  calc
    k ^ 2 ≤ 6 := h
    _ < 9 := by numbers
  cancel 2 at h1
  interval_cases k
  left
  ring
  right
  left
  ring
  right
  right
  ring
  intro h
  cases' h with h h h
  rw [h]
  numbers
  cases' h with h h
  rw [h]
  numbers
  rw [h]
  numbers
