/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · right
      left
      assumption
    · right
      right
      assumption
  · intro h
    cases' h with h h
    . left
      left
      apply h
    cases' h with h h
    . left
      right
      apply h
    right
    right
    assumption


example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have :=
    calc 1 ≡ x [ZMOD 5] := by rel [hx1]
      _ ≡ 2 [ZMOD 5] := by rel [hx2]
    numbers at this
  · intro hx
    contradiction


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  ext t
  dsimp
  suffices -1 < t ∨ t < 1 by exhaust
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]

/-! # Exercises -/


macro "check_equality_of_explicit_sets" : tactic => `(tactic| (ext; dsimp; exhaust))


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = {-1, 4, 3, -2, 2} := by check_equality_of_explicit_sets

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = {0, 2, 4} := by
  check_equality_of_explicit_sets

example : {1, 2} ∩ {3} = {} := by check_equality_of_explicit_sets

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1, 7, 9} := by
  check_equality_of_explicit_sets

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  intro a ha
  dsimp at *
  cases' ha with x hx
  have H : a = 10 * x + 7 := by addarith [hx]
  clear hx
  constructor
  . use a - 5 * x - 4
    rw [H]
    ring
  . use 2 * x + 1
    rw [H]
    ring


example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  intro n hn
  cases' hn with hn5 hn8
  dsimp at *
  cases' hn5 with x hx
  cases' hn8 with y hy
  use 2 * x - 3 * y
  calc
    n = 16 * n - 15 * n := by ring
    _ = 16 * (5 * x) - 15 * n := by rw [hx]
    _ = 16 * (5 * x) - 15 * (8 * y) := by rw [hy]
    _ = 40 * (2 * x - 3 * y) := by ring


example :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  intro n
  dsimp
  intro hn
  intro contra
  cases' contra with y hy
  cases' hn with hn hn <;> cases' hn with x hx
  . rw [hx] at hy
    clear hx n
    have h : (3 * x) ^ 2 -6 * y = 1 := by addarith [hy]
    have temp : (3 * x) ^ 2 -6 * y = 3 * (3 * x ^ 2 - 2 * y) := by ring
    rw [temp] at h
    clear temp hy
    have contra : ¬(3: ℤ) ∣ 1
    . apply Int.not_dvd_of_exists_lt_and_lt
      use 0
      constructor <;> numbers
    apply contra
    use (3 * x ^ 2 - 2 * y)
    rw [h]
  . have goal1 : Int.Even (n ^ 2 - 1)
    . use 3 * y
      rw [hy]
      ring
    have goal2 : Int.Odd (n ^ 2 - 1)
    . rw [hx]
      clear goal1 hx hy
      use 2*x^2 - 1
      ring
    clear hy x hx
    have contra : ¬ Int.Even (n ^ 2 - 1) := by exact (Int.odd_iff_not_even (n ^ 2 - 1)).mp goal2
    contradiction


def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by
  cases' hs with s1 hs1
  cases' hs1 with s2 hs
  cases' hs with hs_ne hs
  cases' hs with hs1 hs2
  cases' ht with t1 ht1
  cases' ht1 with t2 ht
  cases' ht with ht_ne ht
  cases' ht with ht1 ht2
  dsimp [SizeAtLeastTwo] at hst
  dsimp [SizeAtLeastThree]
  by_cases hs1t : s1 ∈ t <;> by_cases hs2t : s2 ∈ t <;> by_cases ht1s : t1 ∈ s <;> by_cases ht2s : t2 ∈ s
  . exfalso
    apply hst
    use s1, s2
    exhaust
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . use s1, s2, t1
    exhaust
