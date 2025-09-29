/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    constructor
    cases' h with h h
    exact h.left
    exact h.left
    cases' h with h h
    left
    exact h.right
    right
    exact h.right


#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  left
  exact h.left


example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  apply h1
  apply h3
  apply h2
  apply h3


example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  cases' h with h1 h2
  contradiction


example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro h
  rw [h1] at h
  contradiction


example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  cases' h1 with h1 h1
  apply h1
  apply h2
  apply h1


example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  intro h
  cases' h with h1 h2
  constructor
  rw [← h]
  apply h1
  apply h2
  intro h
  cases' h with h1 h2
  constructor
  rw [h]
  apply h1
  apply h2


example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  intro h
  apply h.left
  intro h
  constructor <;> assumption


example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor <;>
  . intro h
    cases' h with h h
    right
    apply h
    left
    apply h


example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  intro h
  constructor
  intro h2
  apply h
  left
  apply h2
  intro h2
  apply h
  right
  apply h2
  intro h
  intro h2
  cases' h with hp hq
  cases' h2 with h h
  apply hp
  apply h
  apply hq
  apply h


example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1
  apply h2


example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  intro hx
  cases' hx with x hx
  use x
  rw [← h]
  apply hx
  intro hx
  cases' hx with x hx
  use x
  rw [h]
  apply hx


example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  intro h
  cases' h with x h1
  cases' h1 with y h
  use y
  use x
  apply h
  intro h
  cases' h with y h1
  cases' h1 with x h
  use x
  use y
  apply h


example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  intro h y x
  apply h
  intro h x y
  apply h


example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  intro h
  cases' h with hx hq
  cases' hx with x hx
  use x
  constructor
  apply hx
  apply hq
  intro h
  cases' h with x h
  cases' h with hx hq
  constructor
  use x
  apply hx
  apply hq
