/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 5 -- infoview displays `8`


#check @F -- infoview displays `F : ℕ → ℤ`


def q (x : ℝ) : ℝ := x + 3


#check @q -- infoview displays `q : ℝ → ℝ`


#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`


example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers


def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra


inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer


def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos


example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  use athos, porthos
  dsimp [f] -- optional
  exhaust


example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a
  · exhaust
  · exhaust
  · exhaust


-- better (more automated) version of the previous proof
example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a <;> exhaust


def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos


example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust


example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · use aramis
    exhaust
  · use athos
    exhaust
  · use porthos
    exhaust



example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  intro x1 x2 hx
  dsimp at hx
  have H : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = 0
  · calc (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^ 3 - x2 ^ 3 := by ring
      _ = x1 ^ 3 - x1 ^ 3 := by rw [hx]
      _ = 0 := by ring
  rw [mul_eq_zero] at H
  obtain H1 | H2 := H
  · -- case 1: x1 - x2 = 0
    addarith [H1]
  · -- case 2: x1 ^2 + x1 * x2 + x2 ^ 2  = 0
    by_cases hx1 : x1 = 0
    · -- case 2a: x1 = 0
      have hx2 :=
      calc x2 ^ 3 = x1 ^ 3 := by rw [hx]
        _ = 0 ^ 3 := by rw [hx1]
        _ = 0 := by numbers
      cancel 3 at hx2
      calc x1 = 0 := by rw [hx1]
        _ = x2 := by rw [hx2]
    · -- case 2b: x1 ≠ 0
      have :=
      calc 0 < x1 ^ 2 + ((x1 + x2) ^ 2 + x2 ^ 2) := by extra
          _ = 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) := by ring
          _ = 2 * 0 := by rw [H2]
          _ = 0 := by ring
      numbers at this -- contradiction!

/-! # Exercises -/


example : Injective (fun (x : ℚ) ↦ x - 12) := by
  intro x1 x2 h
  dsimp at h
  addarith [h]


example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 1, 2
  constructor
  . rfl
  . numbers


example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  intro x1 x2 h
  dsimp at h
  have temp : 3 * x1 = 3 * x2 := by addarith [h]
  cancel 3 at temp


example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  intro x1 x2 h
  dsimp at h
  have temp : 3 * x1 = 3 * x2 := by addarith [h]
  cancel 3 at temp


example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  intro x
  dsimp
  use x/2
  ring


example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp [Surjective]
  push_neg
  use 1
  intro a
  have temp : ¬(2: ℤ) ∣ 1
  . apply not_dvd_of_exists_lt_and_lt
    use 0
    constructor <;> numbers
  intro contra
  apply temp
  use a
  rw [contra]


example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  dsimp [Surjective]
  push_neg
  use 2
  intro a
  have H := le_or_lt a 1
  cases' H with h h
  . have goal : a ^ 2 < 2 := by calc
      a ^ 2 ≤ 1 ^ 2 := by rel [h]
      _ = 1 := by ring
      _ < 2 := by numbers
    exact Nat.ne_of_lt goal
  . have goal : a ^ 2 > 2
    . have h2 : 2 ≤ a := by addarith [h]
      calc
        a ^ 2 ≥ 2 ^ 2 := by rel [h2]
        _ = 4 := by ring
        _ > 2 := by numbers
    exact Nat.ne_of_gt goal


inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack


example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  exhaust


example : Surjective h := by
  intro b
  cases b
  . use porthos
    rfl
  . use athos
    rfl


def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by
  intro a1 a2 h
  cases a1 <;> cases a2 <;> exhaust


example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intro a
  cases a <;> exhaust


example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor <;> intro h
  . intro x1 x2 h2
    intro contra
    have goal : x1 = x2
    . apply h
      assumption
    contradiction
  . intro x1 x2 h2
    by_contra h3
    have goal : f x1 ≠ f x2
    . apply h
      assumption
    contradiction


example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intro f hf x1 x2 hf2
  dsimp at hf2
  apply hf
  addarith [hf2]


example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  push_neg
  use fun x ↦ -x
  constructor
  . intro x1 x2 h
    dsimp at h
    addarith [h]
  dsimp [Injective]
  push_neg
  use 1, 2
  constructor
  . ring
  numbers


example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use fun x ↦ x
  constructor
  . intro b
    use b
    ring
  dsimp [Surjective]
  push_neg
  use 1
  intro a
  have temp : ¬(2: ℤ) ∣ 1
  . apply not_dvd_of_exists_lt_and_lt
    use 0
    constructor <;> numbers
  intro contra
  apply temp
  use a
  rw [contra]


example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  push_neg
  use 0
  dsimp [Surjective]
  push_neg
  use 1
  intro a
  conv => ring
  numbers


example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  intro x1 x2 h
  by_contra contra
  have contra2 : x1 ≠ x2 := by exact contra
  clear contra
  have H : x1 > x2 ∨ x2 > x1 := by exact Ne.lt_or_lt (id (Ne.symm contra2))
  clear contra2
  cases' H with H H
  . have goal : f x2 < f x1
    . apply hf
      addarith [H]
    have contra := calc
      f x1 = f x2 := h
      _ < f x1 := goal
    have contra2 : f x1 ≠ f x2 := by exact ne_of_gt (hf x2 x1 H)
    contradiction
  . have goal : f x1 < f x2
    . apply hf
      addarith [H]
    have contra := calc
      f x2 = f x1 := by rw [h]
      _ < f x2 := goal
    have contra2 : f x1 ≠ f x2 := by exact ne_of_lt (hf x1 x2 H)
    contradiction


example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  intro b
  simple_induction b with k hk
  . use x0
    apply h0
  cases' hk with a ha
  use i a
  rw [← ha]
  apply hi
