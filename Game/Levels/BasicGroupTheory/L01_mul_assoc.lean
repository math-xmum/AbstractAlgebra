import Game.Metadata

World "BasicGroupTheory"
Level 1

Title "mul_assoc"

Introduction "Welcome to Group Theory! A **group** is a set $G$ with a binary operation $*$ satisfying three axioms: associativity, existence of an identity element, and existence of inverses.

In this level, the goal is `a * b * c = b * (a * c)`. You have a hypothesis `h : a * b = b * a` in your assumptions panel.

The key tactic here is `rw` (rewrite). Given a proof `h : X = Y`, the command `rw [h]` replaces occurrences of `X` with `Y` in the goal. You can chain multiple rewrites: `rw [h1, h2]`.

We will also use `mul_assoc`, which states `a * b * c = a * (b * c)` for any group elements."

Statement (G : Type*) [Group G] (a b c : G) (h : a * b = b * a) : a * b * c = b * (a * c) := by
  Hint "The goal contains `a * b * c`. Since `h : a * b = b * a`, execute `rw [h]` to replace `a * b` with `b * a`."
  rw [h]
  Hint "Now the goal is `b * a * c = b * (a * c)`. The theorem `mul_assoc` states that `a * b * c = a * (b * c)` for any group elements. Use `rw [mul_assoc]` -- Lean will automatically match the variables."
  rw [mul_assoc]

Conclusion "Well done! You can also solve this in one line: `rw [h, mul_assoc]`.

The `rw` tactic is your main tool for equational reasoning. Combined with group-theoretic lemmas like `mul_assoc`, it lets you transform expressions step by step."

/- Use these commands to add items to the game's inventory. -/

NewTheorem mul_assoc
-- NewDefinition Nat Add Eq
