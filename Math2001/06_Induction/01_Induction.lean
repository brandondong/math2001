/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    use 0
    ring
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      use x
      rw [hx]
    · left
      use x+1
      rw [hx]
      ring


example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  . conv => ring
    extra
  calc
    a ^ (k + 1) = (a ^ k) * a := by ring
    _ ≡ (a ^ k) * b [ZMOD d] := by rel [h]
    _ ≡ (b ^ k) * b [ZMOD d] := by rel [IH]
    _ = b ^ (k + 1) := by ring


example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k ^ 2) := by rel [IH]
      _ = k^2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k^2 + 2 * k + 2 * k := by ring
      _ ≥ k^2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  . numbers
  calc
    3 ^ (k + 1) = 3 ^ k * 3 := by ring
    _ ≥ (k ^ 2 + k + 1) * 3 := by rel [IH]
    _ = (k + 1) ^ 2 + (k + 1) + 1 + 2 * k ^ 2 := by ring
    _ ≥ (k + 1) ^ 2 + (k + 1) + 1 := by extra


example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  . conv => ring
  have h : 0 ≤ 1 + a := by addarith [ha]
  calc
    (1 + a) ^ (k + 1) = (1 + a) ^ k * (1 + a) := by ring
    _ ≥ (1 + k * a) * (1 + a) := by rel [IH]
    _ = 1 + (k + 1) * a + k * a ^ 2 := by ring
    _ ≥ 1 + (k + 1) * a := by extra


example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  . left
    conv => ring
    numbers
  cases' IH with h h
  . right
    calc
      5 ^ (k + 1) = 5 ^ k * 5 := by ring
      _ ≡ 1 * 5 [ZMOD 8] := by rel [h]
      _ = 5 := by ring
  . left
    calc
      5 ^ (k + 1) = 5 ^ k * 5 := by ring
      _ ≡ 5 * 5 [ZMOD 8] := by rel [h]
      _ = 1 + 3 * 8 := by ring
      _ ≡ 1 [ZMOD 8] := by extra


example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  . left
    conv => ring
    numbers
  cases' IH with h h
  . right
    calc
      6 ^ (k + 1) = 6 ^ k * 6 := by ring
      _ ≡ 1 * 6 [ZMOD 7] := by rel [h]
      _ = 6 := by ring
  . left
    calc
      6 ^ (k + 1) = 6 ^ k * 6 := by ring
      _ ≡ 6 * 6 [ZMOD 7] := by rel [h]
      _ = 1 + 5 * 7 := by ring
      _ ≡ 1 [ZMOD 7] := by extra


example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k IH
  . left
    conv => ring
    extra
  cases' IH with h h
  . right
    right
    calc
      4 ^ (k + 1) = 4 ^ k * 4 := by ring
      _ ≡ 1 * 4 [ZMOD 7] := by rel [h]
      _ = 4 := by ring
  cases' h with h h
  . left
    calc
      4 ^ (k + 1) = 4 ^ k * 4 := by ring
      _ ≡ 2 * 4 [ZMOD 7] := by rel [h]
      _ = 1 + 1 * 7 := by ring
      _ ≡ 1 [ZMOD 7] := by extra
  right
  left
  calc
      4 ^ (k + 1) = 4 ^ k * 4 := by ring
      _ ≡ 4 * 4 [ZMOD 7] := by rel [h]
      _ = 2 + 2 * 7 := by ring
      _ ≡ 2 [ZMOD 7] := by extra


example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . numbers
  calc
    3 ^ (k + 1) = 3 ^ k * 3 := by ring
    _ ≥ (2 ^ k + (100:ℤ)) * 3 := by rel [IH]
    _ = 2 ^ (k + 1) + 100 + 2 ^ k + 200 := by ring
    _ ≥ 2 ^ (k + 1) + 100 + 2 ^ k := by extra
    _ ≥ 2 ^ (k + 1) + 100  := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . numbers
  calc
    2 ^ (k + 1) = 2 ^ k * 2 := by ring
    _ ≥ (k ^ 2 + 4) * 2 := by rel [IH]
    _ = k ^ 2 + k * k + 8 := by ring
    _ ≥ k ^ 2 + 10 * k + 8 := by rel [hk]
    _ = (k + 1) ^ 2 + 4 + 8 * k + 3 := by ring
    _ ≥ (k + 1) ^ 2 + 4 + 8 * 10 + 3 := by rel [hk]
    _ ≥ (k + 1) ^ 2 + 4 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . numbers
  calc
    2 ^ (k + 1) = 2 ^ k * 2 := by ring
    _ ≥ (k ^ 3) * 2 := by rel [IH]
    _ = k ^ 3 + k * k ^ 2 := by ring
    _ ≥ k ^ 3 + 10 * k ^ 2 := by rel [hk]
    _ = k ^ 3 + 3 * k ^ 2 + 6 * k * k + k * k := by ring
    _ ≥ k ^ 3 + 3 * k ^ 2 + 6 * 10 * k + 10 * 10 := by rel [hk]
    _ = (k + 1) ^ 3 + 57 * k + 99 := by ring
    _ ≥ (k + 1) ^ 3 + 57 * 10 + 99 := by rel [hk]
    _ = (k + 1) ^ 3 + 669 := by ring
    _ ≥ (k + 1) ^ 3 := by extra


theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with k IH
  . conv => ring
    use 0
    ring
  cases' IH with y hy
  cases' ha with x hx
  use (2 * y * x + y + x)
  calc
    a ^ (k + 1) = (a ^ k) * a := by ring
    _ = (2 * y + 1) * (2 * x + 1) := by rw [hy, hx]
    _ = 2 * (2 * y * x + y + x) + 1 := by ring


theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  by_contra not_even
  have odd : Odd a
  . exact (odd_iff_not_even a).mpr not_even
  clear not_even
  have odd_pow : Odd (a ^ n)
  . apply Odd.pow
    apply odd
  have not_even_pow : ¬ Even (a ^ n)
  . exact (odd_iff_not_even (a ^ n)).mp odd_pow
  contradiction
