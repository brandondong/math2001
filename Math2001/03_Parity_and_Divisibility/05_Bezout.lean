/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  cases' hn with x hx
  use 5*x - 3*n
  calc
    n = 5*(5*n) - 24*n := by ring
    _ = 5*(8*x) - 24*n := by rw [hx]
    _ = _ := by ring


example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  cases' h1 with x hx
  use 2 * x - n
  calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * x) - 5 * n := by rw [hx]
    _ = _ := by ring


example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  cases' hn with x hx
  use 2 * n - x
  calc
    n = 12 * n - (11 * n) := by ring
    _ = 12 * n - 6 * x := by rw [hx]
    _ = _ := by ring


example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  cases' ha with x hx
  use 3 * a - 4 * x
  calc
    a = 21 * a - 4 * (5 * a) := by ring
    _ = 21 * a - 4 * (7 * x) := by rw [hx]
    _ = _ := by ring


example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  cases' h1 with x hx
  cases' h2 with y hy
  use 4 * y - 3 * x
  calc
    n = 28 * n - 27 * n := by ring
    _ = 28 * (9 * y) - 27 * n := by rw [hy]
    _ = 28 * (9 * y) - 27 * (7 * x) := by rw [hx]
    _ = _ := by ring


example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  cases' h1 with x hx
  cases' h2 with y hy
  use 2 * x - 5 * y
  calc
    n = 26 * n - 25 * n := by ring
    _ = 26 * (5 * x) - 25 * n := by rw [hx]
    _ = 26 * (5 * x) - 25 * (13 * y) := by rw [hy]
    _ = _ := by ring
