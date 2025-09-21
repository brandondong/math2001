/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  have h := H m hm_left
  have h2 : m ≤ p
  exact Nat.le_of_dvd hp' hmp
  have h3 := eq_or_lt_of_le h2
  cases' h3 with h3 h3
  right
  assumption
  have h4 := h h3
  contradiction


example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  have h := lt_or_ge a 3
  cases' h with h h
  have h1 : a ≤ 2
  addarith [h]
  have h2 := lt_or_ge b 2
  cases' h2 with h2 h2
  have h3 : b ≤ 1
  addarith [h2]
  clear h
  clear h2
  have h2 := calc
    c ^ 2 = a ^ 2 + b ^ 2 := by addarith [h_pyth]
    _ ≤ 2 ^ 2 + b ^ 2 := by rel [h1]
    _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [h3]
    _ < 3 ^ 2 := by numbers
  cancel 2 at h2
  interval_cases a <;>
  interval_cases b <;>
  interval_cases c <;>
  numbers at h_pyth
  . have h3 := calc
      b ^ 2 < a ^ 2 + b ^ 2 := by extra
      _ = c ^ 2 := by rw [h_pyth]
    cancel 2 at h3
    have h4 : b + 1 ≤ c := by addarith [h3]
    have h5 := calc
      c ^ 2 = a ^ 2 + b ^ 2 := by addarith [h_pyth]
      _ ≤ 2 ^ 2 + b ^ 2 := by rel [h1]
      _ = b ^ 2 + 2 * 2 := by ring
      _ ≤ b ^ 2 + 2 * b := by rel [h2]
      _ < b ^ 2 + 2 * b + 1 := by extra
      _ = (b + 1) ^ 2 := by ring
    cancel 2 at h5
    have h6 := calc
      b + 1 ≤ c := h4
      _ < b + 1 := h5
    have h7 : 1 < 1 := by addarith [h6]
    numbers at h7
  assumption


/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h


example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  . have h2 := calc
      4 ≡ n^2 [ZMOD 5] := by rel [hn]
      _ ≡ 0^2 [ZMOD 5] := by rel [h]
      _ = 0 := by ring
    numbers at h2
  . have h2 := calc
      4 ≡ n^2 [ZMOD 5] := by rel [hn]
      _ ≡ 1^2 [ZMOD 5] := by rel [h]
      _ = 1 := by ring
    numbers at h2
  . left
    assumption
  . right
    assumption
  . have h2 := calc
      4 ≡ n^2 [ZMOD 5] := by rel [hn]
      _ ≡ 4^2 [ZMOD 5] := by rel [h]
      _ = 1 + 5 * 3 := by ring
      _ ≡ 1 [ZMOD 5] := by extra
    numbers at h2


example : Prime 7 := by
  apply prime_test
  numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  use 3
  constructor <;>
  numbers
  use 2
  constructor <;>
  numbers
  use 1
  constructor <;>
  numbers
  use 1
  constructor <;>
  numbers
  use 1
  constructor <;>
  numbers


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  cases' h3 with h3 h3
  . have h4 := calc
      1 < x := h2
      _ = x + 2 - 2 := by ring
      _ = 0 - 2 := by rw [h3]
      _ = -2 := by ring
    numbers at h4
  addarith [h3]


namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  cases' h with h1 h2
  have h3 : Even p ∨ Odd p
  exact even_or_odd p
  cases' h3 with h3 h3
  cases' h3 with x hx
  left
  have h4 : 2 = 1 ∨ 2 = p
  apply h2
  use x
  assumption
  cases' h4 with h4 h4
  . numbers at h4
  . addarith [h4]
  right
  assumption
