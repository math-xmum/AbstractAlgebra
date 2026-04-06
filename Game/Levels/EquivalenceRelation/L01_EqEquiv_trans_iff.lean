import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {S :Type*}


Introduction "
An **equivalence relation** on a type $S$ is a binary relation that satisfies three properties:

- **Reflexivity**: $\\forall x,\\; x = x$
- **Symmetry**: $\\forall x\\, y,\\; x = y \\to y = x$
- **Transitivity**: $\\forall x\\, y\\, z,\\; x = y \\to y = z \\to x = z$

The simplest example is ordinary equality ($=$) itself. In Lean, the type `Equivalence r` bundles these three properties for a relation `r`. The `constructor` tactic in the preamble splits the goal into three subgoals, one per property.

Your task: prove that equality on $S$ is an equivalence relation by handling each subgoal in turn.
"

Statement (preamble := constructor ) : Equivalence (α := S) (· = ·) := by
  Hint "**Reflexivity.** The goal is `∀ (x : S), x = x`. Use `intro x` to pick an arbitrary element of $S$.

The `intro` tactic moves a universally quantified variable (or the antecedent of an implication) from the goal into the local context."
  intro x
  Hint "The goal is now `x = x`. The `rfl` tactic closes any goal of the form `a = a` -- it applies the reflexivity of equality."
  rfl
  Hint "**Symmetry.** The goal is `∀ (x y : S), x = y → y = x`. Use `intro x y hxy` to introduce both variables and the hypothesis that `x = y`."
  intro x y hxy
  Hint "We need to show `y = x`. The `rw` (rewrite) tactic replaces occurrences in the goal: `rw [{hxy}]` substitutes every `x` with `y` (using {hxy} : x = y), turning the goal into `y = y`, which Lean closes automatically."
  rw [hxy]
  Hint "**Transitivity.** The goal is `∀ (x y z : S), x = y → y = z → x = z`. Use `intro x y z hxy hyz` to introduce all three variables and both hypotheses."
  intro x y z hxy hyz
  Hint "We need `x = z`. Rewrite with {hxy} to replace `x` by `y`, turning the goal into `y = z`. Type `rw [{hxy}]`."
  rw [hxy]
  Hint "The goal is now `y = z`, which is exactly the hypothesis {hyz}. Use `exact {hyz}` to close it.

The `exact` tactic finishes a goal by providing a term whose type matches the goal exactly."
  exact hyz


-- NewTactic moved to BasicLean
OnlyTactic intro rfl rw exact unfold
