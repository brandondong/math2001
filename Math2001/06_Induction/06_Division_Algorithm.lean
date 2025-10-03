/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq
import Library.Theory.ModEq.Defs

math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`


theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  . apply lt_fmod_of_neg
    assumption
  . apply lt_fmod_of_neg
    assumption
  . assumption
  . have goal : d ≤ n
    . clear h3 h1
      have h1 := calc
        d * n - d * d = d * (n - d) := by ring
        _ ≤ 0 := h2
      clear h2
      have h2 : -d * d ≤ -d * n := by addarith [h1]
      clear h1
      have hd2 : 0 < -d := by exact Int.neg_pos_of_neg hd
      cancel -d at h2
    cases' lt_or_eq_of_le goal with h h
    . assumption
    . rw [h] at h3
      contradiction
termination_by _ n d hd => 2 * n - d


def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> push_neg at *
  . have IH : T (1 - n) = (1 - n) ^ 2 := by apply T_eq
    rw [IH]
    ring
  . have IH : T (-n) = (-n) ^ 2 := by apply T_eq
    rw [IH]
    ring
  . have goal : n = 0
    . have h3 : n ≥ 0 := by exact Int.nonneg_of_neg_nonpos h2
      clear h2
      interval_cases n
      ring
    rw [goal]
    ring
termination_by _ n => 3 * n - 1


theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  cases' hr with hr1 hr2
  cases' hr2 with hr2 har
  cases' hs with hs1 hs2
  cases' hs2 with hs2 has
  have hrs : r ≡ s [ZMOD b]
  . exact Int.ModEq.trans (id (Int.ModEq.symm har)) has
  clear har has a
  cases' hrs with x hx
  have goal : x = 0
  . have hxb1 := calc
      b * x = r - s := by rw [hx]
      _ ≤ r - 0 := by rel [hs1]
      _ = r := by ring
      _ < b := hr2
      _ = b * 1 := by ring
    cancel b at hxb1
    have hxb2 := calc
      b * x = r - s := by rw [hx]
      _ ≥ 0 - s := by rel [hr1]
      _ = -s := by ring
      _ > -b := by addarith [hs2]
      _ = b * -1 := by ring
    cancel b at hxb2
    interval_cases x
    ring
  rw [goal] at hx
  have dummy : b * 0 = 0 := by ring
  rw [dummy] at hx
  addarith [hx]


example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  dsimp
  constructor
  . constructor
    . apply fmod_nonneg_of_pos
      assumption
    . constructor
      . apply fmod_lt_of_pos
        assumption
      use fdiv a b
      have h2 : fmod a b + b * fdiv a b = a
      . apply fmod_add_fdiv
      addarith [h2]
  intro y hy1
  cases' hy1 with hy1 hy2
  cases' hy2 with hy2 hay
  apply uniqueness y b
  . assumption
  . constructor
    . assumption
    constructor
    . assumption
    exact Int.ModEq.refl y
  . constructor
    . apply fmod_nonneg_of_pos
      assumption
    constructor
    . apply fmod_lt_of_pos
      assumption
    have goal : a ≡ fmod a b [ZMOD b]
    . use fdiv a b
      have h2 : fmod a b + b * fdiv a b = a
      . apply fmod_add_fdiv
      addarith [h2]
    exact Int.ModEq.trans (id (Int.ModEq.symm hay)) goal
