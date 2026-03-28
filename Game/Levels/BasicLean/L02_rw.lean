import Game.Metadata

import Game.Generator.Basic

World "BasicLean"
Level 2

Title "Rewrite"

Introduction "This level gets you familiar with the game interface."

Introduction "The following statement claims that if $x = 2$ and $y = 4$, then $x + x = y$.
This is a simple arithmetic proof showing that the sum of $x$ with itself equals $y$ given the initial conditions."


Statement (x y : ℕ) (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can use rw [h] to rewrite `x` by `2`."
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "rw is the most basic command you can use."

/- Use these commands to add items to the game's inventory. -/
--TacticDoc rw --"rewrite the goal or assumption"
NewTactic rw nth_rw
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
