import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 14

Introduction "Membership in an equivalence class has a clean characterization: `y ∈ Setoid.quot x` if and only if `x ≈ y`. This is essentially true by definition, since `Setoid.quot x = {y | x ≈ y}`.

This level shows that the statement is so definitionally true that `rfl` suffices."

variable {α :Type*} [inst: Setoid α]


Statement (x : α) (y : α): y ∈ Setoid.quot x ↔ x ≈ y := by
  Hint "Both sides of the `↔` are definitionally equal. The `rfl` tactic closes any goal where the left-hand side and right-hand side are the same by definition. Try `rfl`."
  rfl

Conclusion "Since `Setoid.quot x` is defined as `\\{y | x ≈ y\\}`, membership is equivalent to the relation holding. This result is now available as `Setoid.mem_quot_iff_equiv`."

OnlyTactic rewrite rfl
OnlyTheorem Set.mem_setOf_eq
