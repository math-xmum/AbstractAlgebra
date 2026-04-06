import Game.Metadata

import Game.Levels.Lemmas.Group

World "Magma"

Level 1


#check {x : ℝ | x > 0 }
#check mul_pos_iff_of_pos_left
#check mul_pos

open Set

Introduction "
A **magma** is a set equipped with a binary operation that is *closed* under that operation.
More precisely, a set $S$ with an operation $\\cdot$ is a magma if for every $a, b \\in S$,
we have $a \\cdot b \\in S$.

In this level we prove that the positive real numbers $\\{x \\in \\mathbb{R} \\mid x > 0\\}$
form a magma under **multiplication**: the product of two positive reals is again positive.

The definition `Set.isMagma S` unfolds to: for all $x, y \\in S$, we have $x * y \\in S$.
"

Statement : Set.isMagma {x : ℝ | x > 0} := by
  Hint "The goal is `Set.isMagma S` where `S` is the set of positive reals. The tactic `unfold` replaces a definition with its body. Use `unfold Set.isMagma` to expand the definition and see the closure condition explicitly."
  unfold Set.isMagma
  Hint "The goal is now a universal statement: for all `x y` in the set, `x * y` is also in the set. Use `intro x y hx hy` to introduce the elements `x`, `y` and their membership hypotheses `hx : x > 0` and `hy : y > 0`."
  intro x y hx hy
  Hint "The goal says `x * y` is in the set of positive reals. The theorem `Set.mem_setOf_eq` rewrites membership in a set-builder set into the underlying predicate. Use `rw [Set.mem_setOf_eq]` to simplify the goal to `x * y > 0`."
  rw [Set.mem_setOf_eq]
  Hint "We need to show `x * y > 0`. The theorem `mul_pos` states that if `0 < a` and `0 < b` then `0 < a * b`. Use `apply mul_pos` to reduce the goal to two subgoals: `x > 0` and `y > 0`."
  apply mul_pos
  Hint "The first subgoal is `x > 0`, which is exactly our hypothesis `{hx}`. Use `exact hx`."
  exact hx
  Hint "The second subgoal is `y > 0`, which is exactly our hypothesis `{hy}`. Use `exact hy`."
  exact hy

#check Set.isAddMagma

OnlyTactic unfold use rw decide push_neg
NewTheorem Set.mem_setOf_eq mul_pos
OnlyTheorem Set.mem_setOf_eq mul_pos
NewDefinition Set.isMagma Set.isAddMagma
