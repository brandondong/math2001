/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option quotPrecheck false


/-! # Homework 10

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-10,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autograded 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 6 * n ^ 2 ≥ 4 * n } := by
  intro m hm
  dsimp at *
  calc
    m ^ 3 - 6 * m ^ 2 = m * m ^ 2 - 6 * m ^ 2 := by ring
    _ ≥ 10 * m ^ 2 - 6 * m ^ 2 := by rel [hm]
    _ = 4 * m * m := by ring
    _ ≥ 4 * 10 * m := by rel [hm]
    _ = 4 * m + 36 * m := by ring
    _ ≥ 4 * m := by extra


/- Problem 2: prove one of these, delete the other -/

@[autograded 3]
theorem problem2b : { t : ℝ | t ^ 2 - 3 * t + 2 = 0 } ≠ { s : ℝ | s = 2 } := by
  ext
  push_neg
  use 1
  left
  constructor
  . dsimp
    ring
  . dsimp
    numbers


/- Problem 3: prove one of these, delete the other -/

@[autograded 3]
theorem problem3a : {1, 2, 3} ∩ {2, 3, 4} ⊆ {2, 3, 6} := by
  intro a ha
  dsimp at *
  cases' ha with ha1 ha2
  cases' ha1 with ha1 ha1 <;> cases' ha2 with ha2 ha2
  . left
    assumption
  . cases' ha2 with ha2 ha2 <;> rw [ha2] at ha1 <;> numbers at ha1
  . left
    assumption
  . cases' ha1 with ha1 ha1
    . left
      assumption
    . right
      left
      assumption


/- Problem 4 -/

@[autograded 4]
theorem problem4 : { r : ℤ | r ≡ 11 [ZMOD 15] }
    = { s : ℤ | s ≡ 2 [ZMOD 3] } ∩ { t : ℤ | t ≡ 1 [ZMOD 5] } := by
  ext x
  constructor <;> intro h <;> dsimp at *
  . cases' h with y hy
    have hx : x = 15 * y + 11 := by addarith [hy]
    rw [hx]
    constructor
    . use 5 * y + 3
      ring
    . use 3 * y + 2
      ring
  . cases' h with h1 h2
    cases' h1 with a ha
    cases' h2 with b hb
    have ha2 : x = 3 * a + 2 := by addarith [ha]
    have hb2 : x = 5 * b + 1 := by addarith [hb]
    use 2 * b - a - 1
    calc
      x - 11 = 6 * x - 5 * x - 11 := by ring
      _ = 6 * x - 5 * (3 * a + 2) - 11 := by rw [ha2]
      _ = 6 * (5 * b + 1) - 5 * (3 * a + 2) - 11 := by rw [hb2]
      _ = _ := by ring


/-! ### Problem 5 starts here -/


local infix:50 "∼" => fun (a b : ℤ) ↦ ∃ m n, m > 0 ∧ n > 0 ∧ a * m = b * n


/- Problem 5.1: prove one of these, delete the other -/

@[autograded 2]
theorem problem51a : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  use 1, 1
  constructor
  . numbers
  constructor
  . numbers
  rfl


/- Problem 5.2: prove one of these, delete the other -/

@[autograded 2]
theorem problem52a : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  cases' h with m h
  cases' h with n h
  use n, m
  constructor
  . apply h.right.left
  constructor
  . apply h.left
  rw [h.right.right]


/- Problem 5.3: prove one of these, delete the other -/

@[autograded 2]
theorem problem53b : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 2
  constructor
  . use 2, 1
    constructor
    . numbers
    constructor
    . numbers
    ring
  constructor
  . use 1, 2
    constructor
    . numbers
    constructor
    . numbers
    ring
  numbers


/- Problem 5.4: prove one of these, delete the other -/

@[autograded 2]
theorem problem54a : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  intro x y z hxy hyz
  cases' hxy with a hxy
  cases' hxy with b hxy
  cases' hyz with c hyz
  cases' hyz with d hyz
  use a * c, b * d
  cases' hxy with ha hxy
  cases' hyz with hc hyz
  cases' hxy with hb hxy
  cases' hyz with hd hyz
  constructor
  . calc
      a * c > a * 0 := by rel [hc]
      _ = 0 := by ring
  constructor
  . calc
      b * d > b * 0 := by rel [hd]
      _ = 0 := by ring
  calc
    x * (a * c) = x * a * c := by ring
    _ = y * b * c := by rw [hxy]
    _ = y * c * b := by ring
    _ = z * d * b := by rw [hyz]
    _ = _ := by ring


/-! ### Problem 6 starts here -/

infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)


/- Problem 6.1: prove one of these, delete the other -/

@[autograded 2]
theorem problem61a : Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  intro x
  constructor <;> extra


/- Problem 6.2: prove one of these, delete the other -/

@[autograded 2]
theorem problem62b : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use (1,1), (2,2)
  constructor
  . constructor <;> numbers
  . left
    numbers


/- Problem 6.3: prove one of these, delete the other -/

@[autograded 2]
theorem problem63a : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro x y hx hy
  constructor <;> apply le_antisymm
  . apply hx.left
  . apply hy.left
  . apply hx.right
  . apply hy.right


/- Problem 6.4: prove one of these, delete the other -/

@[autograded 2]
theorem problem64a : Transitive (· ≺ ·) := by
  dsimp [Transitive]
  intro x y z hx hy
  constructor
  . calc
      x.1 ≤ y.1 := hx.left
      _ ≤ z.1 := hy.left
  . calc
      x.2 ≤ y.2 := hx.right
      _ ≤ z.2 := hy.right
