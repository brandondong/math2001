/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

open Function


/-! # Homework 9

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-9,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autograded 4]
theorem problem1a : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro b
  use b/2
  ring


/- Problem 2: prove one of these, delete the other -/

@[autograded 4]
theorem problem2b : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp [Surjective]
  push_neg
  use 1
  have f : ¬(2: ℤ) ∣ 1
  . apply Int.not_dvd_of_exists_lt_and_lt
    use 0
    constructor <;> numbers
  intro a
  intro h
  apply f
  use a
  rw [h]


/- Problem 3: prove one of these, delete the other -/

@[autograded 4]
theorem problem3a : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intro f hf
  dsimp [Injective] at *
  intro a1 a2 ha
  apply hf
  addarith [ha]


/- Problem 4: prove one of these, delete the other -/

@[autograded 4]
theorem problem4a : Bijective (fun (x : ℝ) ↦ 3 - 2 * x) := by
  constructor
  . dsimp [Injective]
    intro a1 a2 ha
    have temp : -2 * a1 = -2 * a2 := by addarith [ha]
    cancel -2 at temp
  . dsimp [Surjective]
    intro b
    use (b - 3)/(-2)
    ring


/- Problem 5: prove one of these, delete the other -/

@[autograded 5]
theorem problem5b :
    ¬Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp [Injective]
  push_neg
  use (1,1,1), (0,3,0)
  constructor
  . constructor <;> ring
  numbers


/- Problem 6: prove one of these, delete the other -/

@[autograded 4]
theorem problem6a : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r + 2 * s)) := by
  constructor
  . dsimp [Injective]
    intro a1 a2 ha
    obtain ⟨hm1, hm2⟩ := ha
    constructor
    . rw [hm1] at hm2
      addarith [hm2]
    . apply hm1
  . dsimp [Surjective]
    intro b
    use (b.2 - 2 * b.1, b.1)
    constructor <;> ring
