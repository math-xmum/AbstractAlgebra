import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 8

Title "An Element Belongs to Its Equivalence Class"

Introduction "The equivalence class of x is defined as [x] = {y | x ≈ y}. By reflexivity, x ≈ x, so x is always a member of its own equivalence class."

variable {α : Type*} [Setoid α]

Statement (x : α) : x ∈ {y | x ≈ y} := by
  Hint "The goal asks to show x is in the equivalence class of x, which unfolds to x ≈ x. This is exactly reflexivity of the equivalence relation."
  exact Setoid.refl _

Conclusion "This simple fact — that x ∈ [x] — is the foundation for everything that follows about equivalence classes."

NewTheorem Setoid.refl
OnlyTactic exact
