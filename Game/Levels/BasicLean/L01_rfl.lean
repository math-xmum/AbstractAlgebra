import Game.Metadata
--import Game.Generator.Basic

World "BasicLean"
Level 1

Title "Rfl tactic"

Introduction "Welcome to the game! This first level gets you familiar with the interface.

The goal is to prove that $2 + 2 = 4$. This is a basic arithmetic equality that holds by definition in Lean's natural number system, so the proof requires only simple computation."
Statement : 2 + 2 = 4 := by
  Hint (hidden := true) "**`rfl`** stands for *reflexivity*. It closes any goal of the form `a = a`, where both sides are *definitionally* equal. Lean automatically computes `2 + 2` to `4`, so `rfl` sees that both sides match.

Syntax: just type `rfl`.

Alternatively, `simp` is a powerful tactic that simplifies the goal using known lemmas and computation. It can often close arithmetic goals like this one."
  Branch
    rfl
  simp


Conclusion "Well done! You have learned two tactics:
- **`rfl`** closes goals where both sides are definitionally equal.
- **`simp`** simplifies goals using a library of lemmas and basic computation.

Both are very handy for closing straightforward goals."

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl simp

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
