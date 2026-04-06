import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 12

Introduction "We now introduce the **quotient map** `Setoid.quot`. Given an element `x : α` and a setoid on `α`, `Setoid.quot x` is the equivalence class of `x`, defined as the set `{y | x ≈ y}`. It is bundled as a term of type `Setoid.Equivclass α`, which carries a proof that the set is indeed an equivalence class.

In this level we prove a fundamental fact: every element belongs to its own equivalence class. That is, `x ∈ Setoid.quot x`."

variable {α :Type*} [inst: Setoid α]


Statement
 (x : α) : x ∈ Setoid.quot x  := by
   Hint "The goal is `x ∈ Setoid.quot x`. Since `Setoid.quot x` is defined as the equivalence class of `x`, we can unfold this definition. Use `unfold Setoid.quot` to reveal the underlying set membership."
   unfold Setoid.quot
   Hint "After unfolding, the goal becomes `x ≈ x`, which is reflexivity of the equivalence relation. Use `exact Setoid.refl _` to close it. The `exact` tactic finishes a goal by providing a proof term directly."
   exact Setoid.refl _

Conclusion "Every element belongs to its own equivalence class. This is a direct consequence of reflexivity."


NewDefinition Setoid.quot
NewTheorem Setoid.refl
-- NewTactic moved to BasicLean
OnlyTactic rewrite unfold exact
