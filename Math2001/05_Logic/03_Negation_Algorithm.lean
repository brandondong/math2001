/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h
    intro h2
    cases' h2 with hP hQ
    cases' h with h h <;> contradiction


example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by
  calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
      ↔ ∃ n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬ (n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_exists]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬ n ^ 2 < m ∨ ¬m < (n + 1) ^ 2 := by rel [Decidable.not_and]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by norm_num


#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n ^ 2 = n * n := by ring
      _ ≥ 2 * 2 := by rel [hn]
      _ > 2 := by numbers


/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  intro h
  by_cases hp : P
  apply hp
  exfalso
  apply h
  apply hp
  intro hp
  intro hpp
  contradiction


example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  intro h
  by_cases hp : P
  by_cases hq : Q
  exfalso
  apply h
  intro
  apply hq
  constructor <;> assumption
  exfalso
  apply h
  intro hpp
  contradiction
  intro h
  cases' h with hp hq
  intro h
  apply hq
  apply h
  apply hp


example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  . intro h
    by_cases h2 : ∃ (x : α), ¬P x
    assumption
    exfalso
    apply h
    intro x
    clear h
    by_cases h3 : P x
    assumption
    exfalso
    apply h2
    use x
    apply h3
  intro h
  intro h2
  cases' h with x hx
  apply hx
  apply h2


example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by
  constructor
  intro h
  push_neg at h
  assumption
  intro h
  push_neg
  assumption


example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by
  constructor
  intro h
  push_neg at h
  assumption
  intro h
  push_neg
  assumption


example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by
  constructor
  intro h
  push_neg at h
  assumption
  intro h
  push_neg
  assumption


#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  have lol := lt_or_ge t 5
  cases' lol with h h
  right
  assumption
  left
  calc
   t ≥ 5 := h
   _ > 4 := by numbers


example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  have lol := le_or_lt k 3
  cases' lol with h h
  . apply ne_of_gt
    calc
      2 * k ≤ 2 * 3 := by rel [h]
      _ < 7 := by numbers
  apply ne_of_lt
  have lol : 4 ≤ k := by exact h
  calc
    2 * k ≥ 2 * 4 := by rel [lol]
    _ > 7 := by numbers


example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  constructor
  assumption
  constructor
  assumption
  assumption


example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2 * a ^ 2
  calc
    2 * a ^ 3 = 2 * a ^ 2 * a := by ring
    _ < _ := by extra


example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    apply hp
    clear hp
    dsimp [Prime]
    constructor
    assumption
    intro m hmp
    have lol := Nat.lt_or_ge m 2
    cases' lol with h h
    . interval_cases m
      . right
        cases' hmp with y hy
        have what := calc
          p = 0 * y := hy
          _ = 0 := by ring
        addarith [what]
      . left
        ring
    . have h2 : m ≤ p
      . apply Nat.le_of_dvd
        . calc
            p ≥ 2 := hp2
            _ > 0 := by numbers
        apply hmp
      have lol : m < p ∨ m = p := by exact Nat.lt_or_eq_of_le h2
      cases' lol with lol lol
      . have contra : ¬m ∣ p
        apply H
        assumption
        assumption
        contradiction
      right
      assumption
  push_neg at H
  assumption
