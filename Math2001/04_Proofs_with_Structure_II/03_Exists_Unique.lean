/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  constructor
  intro x hx1 hx2
  have h : (x - 2) ^ 2 ≤ 1 ^ 2
  apply sq_le_sq'
  addarith [hx1]
  addarith [hx2]
  addarith [h]
  intro y h
  have h2 : (3 - y) ^ 2 ≤ 1
  apply h
  numbers
  numbers
  have h3 : (3 - y) ^ 2 ≤ 1 ^ 2 := by addarith [h2]
  cancel 2 at h3
  have h4 : (1 - y) ^ 2 ≤ 1
  apply h
  numbers
  numbers
  have h5 : (1 - y) ^ 2 ≤ 1 ^ 2 := by addarith [h4]
  have h6 : -1 ≤ 1 - y
  have h8 : (0: ℚ) ≤ 1 := by numbers
  have h7 := abs_le_of_sq_le_sq' h5 h8
  cases' h7 with h7 h8
  assumption
  apply le_antisymm
  addarith [h6]
  addarith [h3]


example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  ring
  intro y hy
  calc
    y = (4 * y - 3 + 3) / 4 := by ring
    _ = (9 + 3) / 4 := by rw [hy]
    _ = 3 := by ring


example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  intro x
  extra
  intro y hy
  have h := hy 0
  interval_cases y
  ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  constructor
  constructor
  numbers
  constructor
  numbers
  use 3
  ring
  intro y hy
  cases' hy with hy1 hy2
  cases' hy2 with hy2 hy3
  cases' hy3 with x hx
  have h2 := calc
    3 * x = 11 - y := by addarith [hx]
    _ ≤ 11 - 0 := by rel [hy1]
    _ < 3 * 4 := by numbers
  cancel 3 at h2
  have h3 := calc
    3 * x = 11 - y := by addarith [hx]
    _ > 11 - 3 := by rel [hy2]
    _ > 3 * 2 := by numbers
  cancel 3 at h3
  interval_cases x
  addarith [hx]
