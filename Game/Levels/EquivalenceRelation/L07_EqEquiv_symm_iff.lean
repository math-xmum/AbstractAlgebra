import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 7


variable {α :Type*} [Setoid α]


Introduction "
A **setoid** is a type equipped with an equivalence relation, written `≈` in Lean. Lean's `[Setoid α]` instance provides the relation and proofs of reflexivity, symmetry, and transitivity.

Here we prove that `≈` is symmetric as an iff: $x \\approx y \\iff y \\approx x$. The key lemma is `Setoid.symm`, which states that if `x ≈ y` then `y ≈ x`.

To prove an iff (`↔`), use `constructor` to split it into two implications, then provide each direction.
"

Statement {x y : α} : x ≈ y ↔ y ≈ x := by
  Hint "Use `constructor` to split the iff into two implications (forward and backward)."
  constructor
  Hint "Both directions follow from symmetry. Use `exact Setoid.symm` for the forward direction.

`Setoid.symm` has type `x ≈ y → y ≈ x`. When the goal is an implication and the proof term is a function of the right type, `exact` can supply it directly without `intro`."
  exact Setoid.symm
  Hint "The backward direction is also `exact Setoid.symm`."
  exact Setoid.symm


NewTheorem Setoid.symm
-- NewTactic moved to BasicLean
OnlyTactic intro rfl rw exact unfold constructor
