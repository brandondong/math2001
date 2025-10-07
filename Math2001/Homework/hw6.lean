/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-! # Homework 6

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-6,
for clearer statements and any special instructions. -/

@[autograded 4]
theorem problem1 : ¬ (∃ t : ℝ, t ≤ 5 ∧ 2 * t ≥ 12) := by
  push_neg
  intro t
  cases' le_or_lt t 5 with h h
  . right
    calc
      2 * t ≤ 2 * 5 := by rel [h]
      _ < 12 := by numbers
  . left
    apply h


@[autograded 3]
theorem problem2 : ¬ (∃ x : ℝ, ∀ y : ℝ, y ≤ x) := by
  push_neg
  intro x
  use x + 1
  extra


@[autograded 3]
theorem problem3 (a : ℚ) : 3 * a + 2 < 11 ↔ a < 3 := by
  constructor <;> intro h
  . calc
      a = (3 * a + 2 - 2) / 3 := by ring
      _ < (11 - 2) / 3 := by rel [h]
      _ = 3 := by ring
  . calc
      3 * a + 2 < 3 * 3 + 2 := by rel [h]
      _ = 11 := by ring


@[autograded 6]
theorem problem4 (t : ℤ) : t ^ 2 + t + 3 ≡ 0 [ZMOD 5] ↔ t ≡ 1 [ZMOD 5] ∨ t ≡ 3 [ZMOD 5] := by
  constructor <;> intro h
  . mod_cases t % 5
    . have contra := calc
        0 ≡ t ^ 2 + t + 3 [ZMOD 5] := by rel [h]
        _ ≡ 0 ^ 2 + 0 + 3 [ZMOD 5] := by rel [H]
        _ = 3 := by ring
      numbers at contra
    . left
      apply H
    . have contra := calc
        0 ≡ t ^ 2 + t + 3 [ZMOD 5] := by rel [h]
        _ ≡ 2 ^ 2 + 2 + 3 [ZMOD 5] := by rel [H]
        _ = 4 + 5 * 1 := by ring
        _ ≡ 4 [ZMOD 5] := by extra
      numbers at contra
    . right
      apply H
    . have contra := calc
        0 ≡ t ^ 2 + t + 3 [ZMOD 5] := by rel [h]
        _ ≡ 4 ^ 2 + 4 + 3 [ZMOD 5] := by rel [H]
        _ = 3 + 5 * 4 := by ring
        _ ≡ 3 [ZMOD 5] := by extra
      numbers at contra
  . cases' h with h h
    . calc
        t ^ 2 + t + 3 ≡ 1 ^ 2 + 1 + 3 [ZMOD 5] := by rel [h]
        _ = 0 + 1 * 5 := by ring
        _ ≡ 0 [ZMOD 5] := by extra
    . calc
        t ^ 2 + t + 3 ≡ 3 ^ 2 + 3 + 3 [ZMOD 5] := by rel [h]
        _ = 0 + 3 * 5 := by ring
        _ ≡ 0 [ZMOD 5] := by extra


@[autograded 4]
theorem problem5 (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor <;> intro h <;> constructor <;> cases' h with h1 h2 <;> assumption


@[autograded 5]
theorem problem6 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor <;> intro h
  . cases' h with h q
    cases' h with x hx
    use x
    constructor <;> assumption
  . cases' h with x hx
    constructor
    . use x
      apply hx.left
    . apply hx.right
