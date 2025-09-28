/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel [h5]
      _ = 15 := by ring
    numbers at h


example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  cases' h with n hn
  have h2 := le_or_succ_le n 1
  cases' h2 with h2 h2
  . have h3 := calc
      1 = 1 ^ 2 := by ring
      _ ≥ n ^ 2 := by rel [h2]
      _ = 2 := by rw [hn]
    numbers at h3
  . have h3 := calc
      4 = 2 ^ 2 := by ring
      _ ≤ n ^ 2 := by rel [h2]
      _ = 2 := by rw [hn]
    numbers at h3


example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  . intro h h4
    rw [Int.even_iff_modEq] at h4
    rw [Int.odd_iff_modEq] at h
    have h3 :=
    calc 0 ≡ n [ZMOD 2] := by rel [h4]
      _ ≡ 1 [ZMOD 2] := by rel [h]
    numbers at h3
  . intro h
    obtain h1 | h2 := Int.even_or_odd n
    contradiction
    assumption


example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) ≡ 1 + 3 * 1 [ZMOD 3] := by extra
      _ = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!


example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 := calc
    b*q < a := hq₁
    _ = b*k := hk
  cancel b at h2
  have h3 : q + 1 ≤ k := by addarith [h2]
  have contra := calc
    q + 1 ≤ k := h3
    _ < q + 1 := h1
  have contra2 : 1 < 1 := by addarith [contra]
  numbers at contra2


example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m
    calc
      p = m * l := hl
      _ = l * m := by ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have hl3 : T * l < T * T
    . calc
        T * l ≤ m * l := by rel [hmT]
        _ = p := by rw [hl]
        _ < T ^ 2 := hTp
        _ = T * T := by ring
    cancel T at hl3
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers


/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  cases' h with t ht
  cases' ht with ht1 ht2
  have contra := calc
    4 ≥ t := by rel [ht1]
    _ ≥ 5 := by rel [ht2]
  numbers at contra


example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  cases' h with a ha
  cases' ha with ha1 ha2
  have ha3 := calc
    a ^ 2 ≤ 8 := ha1
    _ < 3 ^ 2 := by numbers
  cancel 2 at ha3
  have la := lt_or_ge a 0
  cases' la with la la
  . have contra : a ^ 3 < 0
    . clear ha3
      clear ha2
      clear ha1
      have h : a ^ 2 > 0
      . exact sq_pos_of_neg la
      have h2 : (a ^ 2) * a < 0 := by exact Linarith.mul_neg la h
      calc
        a ^ 3 = (a ^ 2) * a := by ring
        _ < 0 := h2
    have contra2 := calc
      a ^ 3 < 0 := contra
      _ < 30 := by numbers
    have ha4 : ¬a ^ 3 ≥ 30 := by exact not_le.mpr contra2
    contradiction
  have contra := calc
    a ^ 3 = a * a * a := by ring
    _ < 3 * 3 * 3 := by rel [ha3]
    _ < 30 := by numbers
  have ha4 : ¬a ^ 3 ≥ 30 := by exact not_le.mpr contra
  contradiction


example : ¬ Int.Even 7 := by
  intro h
  cases' h with x hx
  have h2 := le_or_succ_le x 3
  cases' h2 with h2 h2
  . have h3 := calc
      7 = 2 * x := hx
      _ ≤ 2 * 3 := by rel [h2]
    numbers at h3
  . have h3 := calc
      7 = 2 * x := hx
      _ ≥ 2 * 4 := by rel [h2]
    numbers at h3


example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro h
  cases' h with h1 h2
  have hn2 : n = 4 := by addarith [hn]
  rw [hn2] at h2
  numbers at h2


example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro h
  have hx2 : x ^ 2 < 3 ^ 2 := by addarith [hx]
  have dummy : (0: ℝ) ≤ 3 := by numbers
  have hx3 := abs_lt_of_sq_lt_sq' hx2 dummy
  clear dummy
  cases' hx3 with hx3 hx4
  cases' h with hx5 hx5
  . have contra : ¬ -3 < x
    exact not_lt.mpr hx5
    contradiction
  . have contra: ¬ x < 3
    exact not_lt.mpr hx5
    contradiction


example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  cases' h with N hN
  have h1 : Nat.Even (N+1)
  apply hN
  extra
  have h2 : Nat.Even (N+2)
  apply hN
  extra
  clear hN
  rw [Nat.even_iff_not_odd] at h2
  apply h2
  clear h2
  cases' h1 with x hx
  use x
  calc
    N + 2 = N + 1 + 1 := by ring
    _ = 2 * x + 1 := by rw [hx]


example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases hn : n % 4
  . have contra := calc
      2 ≡ n ^ 2 [ZMOD 4] := by rel [h]
      _ = n * n := by ring
      _ ≡ 0 * 0 [ZMOD 4] := by rel [hn]
      _ = 0 := by ring
    numbers at contra
  . have contra := calc
      2 ≡ n ^ 2 [ZMOD 4] := by rel [h]
      _ = n * n := by ring
      _ ≡ 1 * 1 [ZMOD 4] := by rel [hn]
      _ = 1 := by ring
    numbers at contra
  . have contra := calc
      2 ≡ n ^ 2 [ZMOD 4] := by rel [h]
      _ = n * n := by ring
      _ ≡ 2 * 2 [ZMOD 4] := by rel [hn]
      _ = 0 + 4 * 1 := by ring
      _ ≡ 0 [ZMOD 4] := by extra
    numbers at contra
  . have contra := calc
      2 ≡ n ^ 2 [ZMOD 4] := by rel [h]
      _ = n * n := by ring
      _ ≡ 3 * 3 [ZMOD 4] := by rel [hn]
      _ = 1 + 4 * 2 := by ring
      _ ≡ 1 [ZMOD 4] := by extra
    numbers at contra


example : ¬ Prime 1 := by
  intro h
  cases' h with h1 h2
  numbers at h1


example : Prime 97 := by
  apply better_prime_test (T := 10)
  numbers
  numbers
  intro m hm hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  use 48
  constructor <;> numbers
  use 32
  constructor <;> numbers
  use 24
  constructor <;> numbers
  use 19
  constructor <;> numbers
  use 16
  constructor <;> numbers
  use 13
  constructor <;> numbers
  use 12
  constructor <;> numbers
  use 10
  constructor <;> numbers
