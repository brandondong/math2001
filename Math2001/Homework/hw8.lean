/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

macro_rules | `(tactic| gcongr_discharger) => `(tactic| numbers)
math2001_init

namespace Nat

/-! # Homework 8

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-8,
for clearer statements and any special instructions. -/


def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

@[autograded 4]
theorem problem1 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  . rfl
  dsimp [B]
  rw [IH]
  ring


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

@[autograded 4]
theorem problem2 (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  . rfl
  dsimp [S]
  rw [IH]
  ring


def a : ℕ → ℤ
  | 0 => 4
  | n + 1 => 3 * a n - 5

@[autograded 4]
theorem problem3 : forall_sufficiently_large (n : ℕ), a n ≥ 10 * 2 ^ n := by
  dsimp
  use 5
  intro x hx
  induction_from_starting_point x, hx with k hk IH
  . dsimp [a]
    numbers
  dsimp [a]
  calc
    3 * a k - 5 ≥ 3 * (10 * 2 ^ k) - 5 := by rel [IH]
    _ = 10 * 2 ^ (k + 1) + (10 * 2 ^ k) - 5 := by ring
    _ ≥ 10 * 2 ^ (k + 1) + (10 * 2 ^ 5) - 5 := by rel [hk]
    _ = 10 * 2 ^ (k + 1) + 315 := by ring
    _ ≥ 10 * 2 ^ (k + 1) := by extra


def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

@[autograded 4]
theorem problem4 (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  . rfl
  . rfl
  dsimp [c]
  rw [IH1]
  ring


def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

@[autograded 4]
theorem problem5 (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  . rfl
  . rfl
  dsimp [q]
  rw [IH1, IH2]
  ring


@[autograded 5]
theorem problem6 (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  have H := even_or_odd n
  cases' H with H H
  . cases' H with w hw
    rw [hw]
    rw [hw] at hn
    clear hw n
    have r1 : 0 < w
    . cancel 2 at hn
    have IH := problem6 w r1
    cases' IH with a ha
    cases' ha with x hx
    use a+1, x
    constructor
    . apply hx.left
    rw [hx.right]
    ring
  . use 0, n
    constructor
    . apply H
    ring
