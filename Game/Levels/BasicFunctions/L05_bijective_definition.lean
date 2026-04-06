import Game.Metadata

World "BasicFunctions"
Level 5
Title "Definition of bijective function."

Introduction "A function $f : α → β$ is **bijective** if it is both injective and surjective — it pairs up elements of $α$ and $β$ in a one-to-one correspondence.

In Lean 4, `Function.Bijective f` is *defined* as `Function.Injective f ∧ Function.Surjective f`."

Statement {α β : Type} (f : α → β) : Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f := by
  Hint "The goal is a definitional equality: `Function.Bijective f` unfolds to exactly `Function.Injective f ∧ Function.Surjective f`.

Use `rfl` to close it."
  rfl

Conclusion "`Function.Bijective f` is just the conjunction of injectivity and surjectivity. This means that to prove bijectivity, you can use `constructor` to split it into two separate goals."
-- NewTactic moved to BasicLean
