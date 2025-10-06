/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Function


section
variable (n : ℤ)

local infix:50 "∼" => fun (x y : ℤ) ↦ x ≡ y [ZMOD n]

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  apply Int.ModEq.refl

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  apply Int.ModEq.symm

example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  apply Int.ModEq.trans

end


section

local infix:50 "∼" => fun (x y : ℤ) ↦ x ^ 2 = y ^ 2

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  ring

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y hxy
  rw [hxy]

example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  intro x y z hxy hyz
  calc x ^ 2 = y ^ 2 := by rw [hxy]
    _ = z ^ 2 := by rw [hyz]

end


section

class Relation (α : Type) where r : α → α → Prop

open Relation

local infix:50 " ∼ " => r

variable {α : Type} [Relation α]

notation:arg "⦍" a "⦐" => { b | a ∼ b }

theorem EquivalenceClass.eq_of_rel (h_symm : @Symmetric α r) (h_trans : @Transitive α r)
    {a1 a2 : α} (ha : a1 ∼ a2) :
    ⦍a1⦐ = ⦍a2⦐ := by
  ext b
  dsimp
  constructor
  · intro ha1b
    apply h_trans (y := a1)
    · apply h_symm ha
    · apply ha1b
  · intro ha2b
    apply h_trans ha ha2b


theorem EquivalenceClass.mem_self (h_refl : @Reflexive α r) (a : α) :
    a ∈ { b : α | a ∼ b } := by
  dsimp
  apply h_refl

end


section

local infix:50 "∼" => fun ((a, b) : ℤ × ℕ) (c, d) ↦ a * (d + 1) = c * (b + 1)

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro (a, b)
  dsimp

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro (a, b) (c, d) h
  dsimp at *
  rw [h]

example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  intro (a, b) (c, d) (e, f) h1 h2
  dsimp at *
  set B := (b:ℤ) + 1
  set D := (d:ℤ) + 1
  set F := (f:ℤ) + 1
  have :=
  calc D * (a * F) = (a * D) * F := by ring
    _ = (c * B) * F := by rw [h1]
    _ = (c * F) * B := by ring
    _ = (e * D) * B := by rw [h2]
    _ = D * (e * B) := by ring
  cancel D at this

end


section

local infix:50 "∼" => fun (α β : Type) ↦ ∃ f : α → β, Bijective f

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro α
  use id
  rw [bijective_iff_exists_inverse]
  use id
  constructor
  · rfl
  · rfl

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro α β h
  obtain ⟨f, hf⟩ := h
  rw [bijective_iff_exists_inverse] at hf
  obtain ⟨g, hfg1, hfg2⟩ := hf
  use g
  rw [bijective_iff_exists_inverse]
  use f
  constructor
  · apply hfg2
  · apply hfg1

example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  intro α β γ h1 h2
  obtain ⟨f1, hf1a, hf1b⟩ := h1
  obtain ⟨f2, hf2a, hf2b⟩ := h2
  use f2 ∘ f1
  constructor
  · apply Injective.comp
    · apply hf2a
    · apply hf1a
  · apply Surjective.comp
    · apply hf2b
    · apply hf1b

end
/-! # Exercises -/


section
local infix:50 "∼" => fun (a b : ℤ) ↦ ∃ m n, m > 0 ∧ n > 0 ∧ a * m = b * n

example : Reflexive (· ∼ ·) := by
  intro x
  dsimp
  use 1, 1
  constructor
  . numbers
  constructor
  . numbers
  ring


example : Symmetric (· ∼ ·) := by
  intro x y
  dsimp
  intro h
  cases' h with m h2
  cases' h2 with n h
  use n, m
  exhaust


example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  intro x y z hx hy
  cases' hx with a ha
  cases' ha with b h1
  cases' hy with c hc
  cases' hc with d h2
  use a*c, d*b
  cases' h1 with ha h1
  cases' h2 with hc h2
  cases' h2 with hd h2
  cases' h1 with hb h1
  constructor
  . calc
      a * c > 0 * c := by rel [ha]
      _ = 0 := by ring
  constructor
  . calc
      d * b > 0 * b := by rel [hd]
      _ = 0 := by ring
  calc
    x * (a * c) = (x * a) * c := by ring
    _ = (y * b) * c := by rw [h1]
    _ = (y * c) * b := by ring
    _ = (z * d) * b := by rw [h2]
    _ = _ := by ring


end


section
local infix:50 "∼" => fun ((a, b) : ℕ × ℕ) (c, d) ↦ a + d = b + c

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  ring


example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  addarith [h]


example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  intro x y z hx hy
  have temp := calc
    x.1 + y.2 + (y.1 + z.2) = x.2 + y.1 + (y.1 + z.2) := by rw [hx]
    _ = x.2 + y.1 + (y.2 + z.1) := by rw [hy]
  addarith [temp]


end


section
local infix:50 "∼" => fun ((a, b) : ℤ × ℤ) (c, d) ↦
  ∃ m n, m > 0 ∧ n > 0 ∧ m * b * (b ^ 2 - 3 * a ^ 2) = n * d * (d ^ 2 - 3 * c ^ 2)

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  use 1, 1
  constructor
  . numbers
  constructor
  . numbers
  ring


example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  cases' h with m h
  cases' h with n h
  use n, m
  exhaust


example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  intro x y z hx hy
  cases' hx with a ha
  cases' ha with b h1
  cases' hy with c hc
  cases' hc with d h2
  cases' h1 with ha h1
  cases' h2 with hc h2
  cases' h2 with hd hyz
  cases' h1 with hb hxy
  use a*c, d*b
  constructor
  . calc
      a * c > 0 * c := by rel [ha]
      _ = 0 := by ring
  constructor
  . calc
      d * b > 0 * b := by rel [hd]
      _ = 0 := by ring
  calc
    a * c * x.2 * (x.2 ^ 2 - 3 * x.1 ^ 2) = c * (a * x.2 * (x.2 ^ 2 - 3 * x.1 ^ 2)) := by ring
    _ = c * (b * y.2 * (y.2 ^ 2 - 3 * y.1 ^ 2)) := by rw [hxy]
    _ = b * (c * y.2 * (y.2 ^ 2 - 3 * y.1 ^ 2)) := by ring
    _ = b * (d * z.2 * (z.2 ^ 2 - 3 * z.1 ^ 2)) := by rw [hyz]
  ring


end
