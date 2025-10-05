/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Set


#check {n : ℤ | n ≤ 3}


example : 1 ∈ {n : ℤ | n ≤ 3} := by
  dsimp
  numbers


namespace Nat
example : 10 ∉ {n : ℕ | Odd n} := by
  dsimp
  rw [← even_iff_not_odd]
  use 5
  numbers
end Nat


example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  dsimp [Set.subset_def] -- optional
  intro a ha
  obtain ⟨k, hk⟩ := ha
  use 2 * k
  calc a = 4 * k := hk
    _ = 2 * (2 * k) := by ring


example : {x : ℝ | 0 ≤ x ^ 2} ⊈ {t : ℝ | 0 ≤ t} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  constructor
  · numbers
  · numbers


example : {x : ℤ | Int.Odd x} = {a : ℤ | ∃ k, a = 2 * k - 1} := by
  ext x
  dsimp
  constructor
  · intro h
    obtain ⟨l, hl⟩ := h
    use l + 1
    calc x = 2 * l + 1 := by rw [hl]
      _ = 2 * (l + 1) - 1 := by ring
  · intro h
    obtain ⟨k, hk⟩ := h
    use k - 1
    calc x = 2 * k - 1 := by rw [hk]
      _ = 2 * (k - 1) + 1 := by ring


example : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  ext
  dsimp
  push_neg
  use 6
  right
  constructor
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 1
    constructor <;> numbers
  · use 3
    numbers


example : {k : ℤ | 8 ∣ 5 * k} = {l : ℤ | 8 ∣ l} := by
  ext n
  dsimp
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


example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc x ^ 2 - x - 2 = (-1) ^ 2 - (-1) - 2 := by rw [h]
        _ = 0 := by numbers
    · calc x ^ 2 - x - 2 = 2 ^ 2 - 2 - 2 := by rw [h]
        _ = 0 := by numbers


example : {1, 3, 6} ⊆ {t : ℚ | t < 10} := by
  dsimp [Set.subset_def]
  intro t ht
  obtain h1 | h3 | h6 := ht
  · addarith [h1]
  · addarith [h3]
  · addarith [h6]

/-! # Exercises -/


example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  numbers


example : 6 ∈ {n : ℕ | n ∣ 42} := by
  use 7
  ring


example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor <;> numbers


example : 11 ∈ {n : ℕ | Odd n} := by
  use 5
  ring


example : -3 ∈ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  dsimp
  intro y
  calc
    -3 ≤ 0 := by numbers
    _ ≤ y ^ 2 := by extra


example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  intro a ha
  dsimp at *
  cases' ha with x hx
  use x*4
  rw [hx]
  ring


example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  . use 1
    ring
  apply Nat.not_dvd_of_exists_lt_and_lt
  use 0
  constructor <;> numbers


example : {r : ℤ | 3 ∣ r} ⊈ {s : ℤ | 0 ≤ s} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  constructor
  . use -1
    ring
  numbers


example : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  intro m hm
  dsimp at *
  calc
    m ^ 3 - 7 * m ^ 2 = m * m ^ 2 - 7 * m ^ 2 := by ring
    _ ≥ 10 * m ^ 2 - 7 * m ^ 2 := by rel [hm]
    _ = 3 * m * m := by ring
    _ ≥ 3 * 10 * m := by rel [hm]
    _ = 4 * m + 26 * m := by ring
    _ ≥ 4 * m := by extra


namespace Int
example : {n : ℤ | Even n} = {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  ext n
  constructor <;> intro hn <;> dsimp at *
  . cases' hn with x hx
    use x-3
    rw [hx]
    ring
  . cases' hn with x hx
    use x+3
    have temp : n = 2 * x + 6 := by addarith [hx]
    rw [temp]
    ring
end Int


example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4} := by
  ext
  push_neg
  use 1
  dsimp
  left
  constructor
  . ring
  numbers


example : {k : ℤ | 8 ∣ 6 * k} ≠ {l : ℤ | 8 ∣ l} := by
  ext
  push_neg
  dsimp
  use 4
  left
  constructor
  . use 3
    ring
  apply Int.not_dvd_of_exists_lt_and_lt
  use 0
  constructor <;> numbers


example : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  ext k
  dsimp
  constructor <;> intro hk
  . cases' hk with x hx
    use 4 * k - 3 * x
    calc
      k = 7 * 4 * k - 3 * (9 * k) := by ring
      _ = 7 * 4 * k - 3 * (7 * x) := by rw [hx]
      _ = 7 * (4 * k - 3 * x) := by ring
  . cases' hk with x hx
    use 9 * x
    rw [hx]
    ring


example : {1, 2, 3} ≠ {1, 2} := by
  ext
  push_neg
  use 3
  left
  constructor
  . dsimp
    right
    right
    rfl
  dsimp
  push_neg
  constructor <;> numbers


example : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  ext x
  dsimp
  constructor <;> intro hx
  . have factored := calc
      (x + 1) * (x + 2) = x ^ 2 + 3 * x + 2 := by ring
      _ = 0 := hx
    cases' eq_zero_or_eq_zero_of_mul_eq_zero factored with h h
    . left
      addarith [h]
    . right
      addarith [h]
  . cases' hx with hx hx <;> rw [hx] <;> ring
