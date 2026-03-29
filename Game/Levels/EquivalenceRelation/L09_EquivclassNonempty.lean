import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 9

Title "Equivalence Classes Are Nonempty"

Introduction "Since x always belongs to [x] (as we proved in the previous level), the equivalence class [x] is never empty. This property is essential: a partition must consist of nonempty sets."

variable {α : Type*} [Setoid α]

Statement (x : α) : {y | x ≈ y} ≠ ∅ := by
  Hint "The equivalence class is nonempty because x ≈ x. This is `Setoid.equivclass_nonempty`."
  exact Setoid.equivclass_nonempty x

Conclusion "Equivalence classes are always nonempty — a crucial ingredient for showing they form a partition."

NewTactic «have»
OnlyTactic intro exact rw «have»
