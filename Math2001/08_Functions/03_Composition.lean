/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init
set_option pp.funBinderTypes true

open Function


def f (a : ℝ) : ℝ := a + 3
def g (b : ℝ) : ℝ := 2 * b
def h (c : ℝ) : ℝ := 2 * c + 6

example : g ∘ f = h := by
  ext x
  calc (g ∘ f) x = g (f x) := by rfl
    _ = 2 * (x + 3) := by rfl
    _ = 2 * x + 6 := by ring
    _ = h x := by rfl


def s (x : ℝ) : ℝ := 5 - x

example : s ∘ s = id := by
  ext x
  dsimp [s]
  ring


def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id


inductive Humour
  | melancholic
  | choleric
  | phlegmatic
  | sanguine
  deriving DecidableEq

open Humour


def p : Humour → Humour
  | melancholic => choleric
  | choleric => sanguine
  | phlegmatic => phlegmatic
  | sanguine => melancholic


def q : Humour → Humour
  | melancholic => sanguine
  | choleric => melancholic
  | phlegmatic => phlegmatic
  | sanguine => choleric

example : Inverse p q := by
  constructor
  · ext x
    cases x <;> exhaust
  · ext x
    cases x <;> exhaust


theorem exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨h_inj, h_surj⟩ := hf
  dsimp [Surjective] at h_surj
  choose g hg using h_surj
  use g
  dsimp [Inverse]
  constructor
  · -- prove `g ∘ f = id`
    ext x
    dsimp [Injective] at h_inj
    apply h_inj
    calc f ((g ∘ f) x) = f (g (f x)) := by rfl
      _ = f x := by apply hg
      _ = f (id x) := by rfl
  · -- prove `f ∘ g = id`
    ext y
    apply hg


theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by rfl
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rfl
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rfl
      _ = id x2 := by rw [hgf]
      _ = x2 := by rfl
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rfl
      _ = id y := by rw [hfg]
      _ = y := by rfl


theorem bijective_iff_exists_inverse (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g := by
  constructor
  · apply exists_inverse_of_bijective
  · intro h
    obtain ⟨g, H⟩ := h
    apply bijective_of_inverse H


/-! # Exercises -/


def a : Humour → Humour
  | melancholic => sanguine
  | choleric => choleric
  | phlegmatic => phlegmatic
  | sanguine => melancholic

def b : Humour → Humour
  | melancholic => phlegmatic
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => sanguine

def c : Humour → Humour
  | melancholic => sanguine
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => phlegmatic

example : b ∘ a = c := by
  ext x
  cases x <;> exhaust


def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x-1)/5

example : Inverse u v := by
  constructor <;> ext x
  . dsimp
    dsimp [u, v]
    ring
  . dsimp
    dsimp [u, v]
    ring


example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  intro a1 a2 h
  dsimp [Injective] at *
  have h2 : (f a1) = (f a2)
  . apply hg
    assumption
  apply hf
  assumption


example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intro b
  dsimp [Surjective] at *
  have hy := hg b
  cases' hy with y hy
  rw [← hy]
  have hx := hf y
  cases' hx with x hx
  use x
  rw [hx]


example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at hf
  choose g hg using hf
  use g
  ext x
  dsimp
  apply hg


example {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at *
  exhaust


example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  have hf := bijective_of_inverse h1
  dsimp [Bijective] at hf
  cases' hf with f_inj f_surj
  ext y
  have hx := f_surj y
  cases' hx with x hx
  rw [← hx]
  dsimp [Inverse] at *
  cases' h1 with h1 h12
  cases' h2 with h2 h22
  clear h12 h22
  calc
    g1 (f x) = (g1 ∘ f) x := by rfl
    _ = id x := by rw [h1]
    _ = (g2 ∘ f) x := by rw [h2]
    _ = g2 (f x) := by rfl
