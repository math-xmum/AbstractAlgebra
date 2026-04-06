import Game.Metadata

import Game.Levels.Lemmas.Group

World "Magma"

Level 6

Introduction "
The integers under the binary operation of **subtraction** ($-$) form a magma
(subtraction of two integers is an integer), but subtraction is **not associative**.
We prove this by finding a counterexample:
integers $a, b, c$ with $(a - b) - c \\neq a - (b - c)$.

This is an existential proof, so we use the `use` tactic to supply witnesses, then `decide`
to verify the arithmetic.
"

Statement : ∃ (a b c : ℤ),  (a - b) - c ≠ a - (b - c )  := by
  Hint "The goal is `∃ (a b c : ℤ), (a - b) - c ≠ a - (b - c)`. The `use` tactic provides witnesses for existential goals. Try `use 2, 1, 1` -- then $(2-1)-1 = 0$ but $2-(1-1) = 2$."
  use 2,1,1
  Hint "The goal is now the concrete inequality `(2 - 1) - 1 ≠ 2 - (1 - 1)`. Since both sides are integer literals, `decide` can verify this automatically. Use `decide`."
  decide

OnlyTactic use decide


