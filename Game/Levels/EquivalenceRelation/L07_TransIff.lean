import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 7

Title "Transitivity Rewriting"

Introduction "If x ≈ y, then x and y are 'interchangeable' in the equivalence relation: x ≈ z if and only if y ≈ z. This is a direct consequence of symmetry and transitivity."

variable {α : Type*} [Setoid α]

Statement {x y z : α} (H : x ≈ y) : x ≈ z ↔ y ≈ z := by
  Hint "We need to prove an iff statement. Use `constructor` to split into two directions."
  constructor
  Hint "For the forward direction, assume x ≈ z and derive y ≈ z. Since y ≈ x (by symmetry) and x ≈ z, transitivity gives y ≈ z."
  · intro H2
    exact Setoid.trans (Setoid.symm H) H2
  Hint "For the backward direction, assume y ≈ z and derive x ≈ z. Since x ≈ y and y ≈ z, transitivity gives x ≈ z."
  · intro H2
    exact Setoid.trans H H2

Conclusion "Well done! This 'rewriting' property is extremely useful: it lets us substitute equivalent elements freely."

NewTheorem Setoid.trans
NewTactic «intro» rfl rw exact constructor
OnlyTactic intro rfl rw exact constructor
