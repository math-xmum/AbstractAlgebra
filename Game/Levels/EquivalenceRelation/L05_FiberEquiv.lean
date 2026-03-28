import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 5


variable {S :Type*}


Statement (preamble := constructor ) (β : Type*) (f : S → β): Equivalence (α := S) (f · = f ·) := by
  intro x
  rfl
  intro x y hxy
  exact hxy.symm
  intro x y z hxy hyz
  rw [hxy]
  exact hyz

NewTactic «intro» rfl rw exact unfold
OnlyTactic intro rfl rw exact unfold
