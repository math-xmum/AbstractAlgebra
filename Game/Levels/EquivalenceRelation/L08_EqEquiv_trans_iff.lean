import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 8


variable {α :Type*} [Setoid α]


Introduction "
If $x \\approx y$, then being equivalent to $z$ from $x$ is the same as being equivalent to $z$ from $y$. Formally: given `H : x ≈ y`, we prove `x ≈ z ↔ y ≈ z`.

The key lemmas are:
- `Setoid.trans : x ≈ y → y ≈ z → x ≈ z` (transitivity)
- `Setoid.symm : x ≈ y → y ≈ x` (symmetry)

You can compose these: `Setoid.trans (Setoid.symm H) H2` chains symmetry of `H` with `H2`.
"

Statement {x y z : α} (H : x ≈ y) : x ≈ z ↔ y ≈ z := by
  Hint "Use `constructor` to split the iff into two implications."
  constructor
  Hint "**Forward:** Assume `H2 : x ≈ z` and prove `y ≈ z`. Use `intro H2`. Then chain: from `H : x ≈ y` get `y ≈ x` by `Setoid.symm H`, then compose with `H2 : x ≈ z` via `Setoid.trans`.

Use `exact Setoid.trans (Setoid.symm H) H2`."
  intro H2
  exact Setoid.trans (Setoid.symm H) H2
  Hint "**Backward:** Assume `H2 : y ≈ z` and prove `x ≈ z`. Chain `H : x ≈ y` with `H2` directly.

Use `intro H2` then `exact Setoid.trans H H2`."
  intro H2
  exact Setoid.trans H H2

NewTheorem Setoid.symm Setoid.trans
-- NewTactic moved to BasicLean
OnlyTactic intro rfl rw exact unfold constructor
