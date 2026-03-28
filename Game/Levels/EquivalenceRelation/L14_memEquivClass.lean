import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 14


variable {α :Type*} [inst: Setoid α]


Statement (x : α) (y : α): y ∈ Setoid.quot x ↔ x ≈ y := by
  rfl

OnlyTactic rewrite rfl
OnlyTheorem Set.mem_setOf_eq
