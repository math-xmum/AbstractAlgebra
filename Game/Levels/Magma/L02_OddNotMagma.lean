import Game.Metadata

import Game.Levels.Lemmas.Group

World "Magma"

Level 2

open Set

/-
#check {x : ℝ | x > 0 }
#check mul_pos
-/

/-
#Genhint
Statement : ¬ Set.isAddMagma {x : ℤ | Odd x} := by
  unfold isAddMagma
  push_neg
  use 1,1
  decide
-/


Introduction "
We saw that positive reals form a magma under multiplication. But not every set is closed
under a given operation.

Here we prove that the odd integers do **not** form a magma under **addition**:
there exist odd integers whose sum is even, so the set is not closed under $+$.

The definition `Set.isAddMagma S` says: for all $x, y \\in S$, we have $x + y \\in S$.
To disprove this, we must show its negation.
"

Statement : ¬ Set.isAddMagma {x : ℤ | Odd x} := by
  Hint "The goal is `¬ Set.isAddMagma S` where `S` is the set of odd integers. Start by expanding the definition with `unfold isAddMagma`."
  unfold isAddMagma
  Hint "The goal is `¬ (∀ x y, ...)`. The tactic `push_neg` pushes the negation `¬` through quantifiers and connectives, turning `¬ ∀` into `∃ ... ¬`. Use `push_neg` to convert this into an existential statement."
  push_neg
  Hint "Now we need to provide a concrete counterexample: two odd integers whose sum is not odd. Since $1 + 1 = 2$ is even, use `use 1, 1`."
  use 1,1
  Hint "The remaining goal is a concrete arithmetic statement: $1$ is odd, $1$ is odd, and $1 + 1$ is not odd. The tactic `decide` can automatically verify decidable propositions like these. Use `decide`."
  decide

-- NewTactic moved to BasicLean
NewDefinition Set.isAddMagma
OnlyDefinition Set.isAddMagma
OnlyTactic unfold use rw decide push_neg
