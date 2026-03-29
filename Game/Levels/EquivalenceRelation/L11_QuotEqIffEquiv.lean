import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 11

Title "Quotient Equality Characterizes Equivalence"

Introduction "We define the quotient map quot : α → α/≈ that sends each element to its equivalence class. Two elements x and y have the same image under quot if and only if x ≈ y. This is the fundamental property of quotients."

variable {α : Type*} [Setoid α]

Statement {x y : α} : Setoid.quot x = Setoid.quot y ↔ x ≈ y := by
  Hint "This follows directly from the fact that two equivalence classes are equal if and only if their representatives are equivalent. Use `simp` with `Setoid.equivclass_eq_iff_equiv`."
  simp [Setoid.equivclass_eq_iff_equiv (α := α)]

Conclusion "This characterization is the bridge between the 'set-theoretic' world of equivalence classes and the 'algebraic' world of the equivalence relation."

NewDefinition Setoid.quot
NewTheorem Setoid.equivclass_eq_iff_equiv
OnlyTactic simp rw
