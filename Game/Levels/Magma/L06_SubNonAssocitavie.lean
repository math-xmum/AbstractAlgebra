import Game.Metadata

import Game.Levels.Lemmas.Group

World "Magma"

Level 6
Title "Subtraction is not associative"

Introduction "The following statement claims that there exist integers $a$, $b$, and $c$ such that $(a - b) - c ≠ a - (b - c)$. This shows that subtraction is not associative."

Statement : ∃ (a b c : ℤ),  (a - b) - c ≠ a - (b - c )  := by
  Hint "We need to find specific values for $a$, $b$, and $c$ that make the statement true. Let's try some simple values like 2, 1, and 1. You can use `use` to provide these values."
  use 2,1,1
  Hint "Now we need to prove that $2 - 1 - 1 ≠ 2 - (1 - 1)$. The left side simplifies to $0$ and the right side to $2$. You can use `decide` to let Lean automatically check this inequality."
  decide

Conclusion "You showed (2-1)-1 = 0 but 2-(1-1) = 2, so subtraction fails associativity. This is why (ℤ, −) is a magma but not a semigroup."

OnlyTactic use decide


