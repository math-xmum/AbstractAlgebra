import Game.Metadata

World "BasicFunctions"
Level 3
Title "Definition of surjective function."

Introduction "A function $f : α → β$ is **surjective** (onto) if every element of the codomain is hit by some element of the domain. Formally, for every $y : β$, there exists $x : α$ such that $f(x) = y$.

In Lean 4, `Function.Surjective f` is *defined* as `∀ y, ∃ x, f x = y`."

Statement {α β γ : Type} (f : α → β) : Function.Surjective f ↔ ∀ y, ∃ x, f x = y := by
  Hint "The goal `Function.Surjective f ↔ ∀ y, ∃ x, f x = y` is again a definitional equality — the left side unfolds to exactly the right side.

Use `rfl` to close the goal."
  rfl


Conclusion "Just like injectivity, `Function.Surjective f` is definitionally `∀ y, ∃ x, f x = y`, so `rfl` works immediately."
