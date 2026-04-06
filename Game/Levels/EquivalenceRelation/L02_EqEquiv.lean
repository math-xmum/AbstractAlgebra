import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 2


variable {α :Type*}


Introduction "
This level is the same proof as Level 1, but now the type is called `α` instead of `S`. The mathematics is identical: we prove that equality on any type is an equivalence relation.

Practice the same pattern: `constructor` splits the goal into reflexivity, symmetry, and transitivity. Then use `intro`, `rfl`, `rw`, and `exact` to handle each case.
"

Statement (preamble := constructor ) : Equivalence (α := α) (· = ·) := by
  Hint "**Reflexivity.** Introduce an arbitrary element with `intro x`, then close `x = x` with `rfl`."
  intro x
  Hint (hidden := true) "Use `rfl` to close `x = x`."
  rfl
  Hint "**Symmetry.** Introduce variables and the hypothesis with `intro x y hxy`, then `rw [hxy]` turns `y = x` into `y = y`."
  intro x y hxy
  Hint (hidden := true) "Use `rw [{hxy}]` to rewrite the goal."
  rw [hxy]
  Hint "**Transitivity.** Introduce everything with `intro x y z hxy hyz`, rewrite with `rw [hxy]`, then finish with `exact hyz`."
  intro x y z hxy hyz
  Hint (hidden := true) "Use `rw [{hxy}]` to turn the goal into `y = z`."
  rw [hxy]
  Hint (hidden := true) "Now use `exact {hyz}`."
  exact hyz


-- NewTactic moved to BasicLean
OnlyTactic intro rfl rw exact unfold
