import Game.Metadata

-- import Game.Generator.Basic

World "BasicLean"
Level 2

Title "Rewrite"

Introduction "In this level you will learn the `rw` (rewrite) tactic, one of the most frequently used tactics in Lean.

The goal is to prove that if $x = 2$ and $y = 4$, then $x + x = y$. You will use hypotheses to substitute values into the goal until it becomes trivially true."

variable (x y : Nat)

Statement (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "**`rw`** (rewrite) replaces occurrences of the left-hand side of an equation with its right-hand side in the goal.

Syntax: `rw [h]` where `h` is a hypothesis of the form `a = b`. This replaces every `a` in the goal with `b`.

You can start with either `rw [{h}]` to replace `x` with `2`, or `rw [{g}]` to replace `y` with `4`."
  Branch
    rw [g]
    Hint "Good. Now the goal still contains `x`. Use `rw [{h}]` to substitute `x` with `2`."
    rw [h]
  rw [h]
  Hint "Good. Now the goal still contains `y`. Use `rw [{g}]` to substitute `y` with `4`. After rewriting, `rw` will automatically close the goal by `rfl` if both sides become definitionally equal."
  rw [g]

Conclusion "Well done! Key points about `rw`:
- `rw [h]` rewrites the goal using hypothesis `h : a = b`, replacing `a` with `b`.
- After rewriting, `rw` automatically tries `rfl` to close the goal.
- If you want to rewrite without the automatic `rfl` step, use `rewrite` instead.
- You can rewrite multiple hypotheses at once: `rw [h, g]`.

These are among the most fundamental tactics you will use in Lean."

/- Use these commands to add items to the game's inventory. -/
--TacticDoc rw --"rewrite the goal or assumption"
NewTactic rw rewrite
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
