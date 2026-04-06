import Game.Metadata

World "BasicFunctions"
Level 1
Title "Definition of injective function."

Introduction "A function $f : α → β$ is **injective** (one-to-one) if distinct inputs always produce distinct outputs. Equivalently, whenever $f(x) = f(y)$, we must have $x = y$.

In Lean 4, `Function.Injective f` is *defined* as `∀ x y, f x = f y → x = y`. Since the goal is this exact definition, both sides of the `↔` are definitionally equal."
Statement {α β γ : Type} (f : α → β) (g : β → γ) : Function.Injective f ↔ ∀ x y, f x = f y → x = y := by
  Hint "The goal `Function.Injective f ↔ ∀ x y, f x = f y → x = y` is a **definitional equality** — the left side unfolds to exactly the right side.

The `rfl` tactic closes any goal of the form `a = a` or `a ↔ a`, including when both sides are definitionally equal. Try `rfl`."
  rfl


Conclusion "Nicely done! You have seen that `Function.Injective f` is defined as `∀ x y, f x = f y → x = y`. The `rfl` tactic works here because both sides are the same by definition."

-- NewTactic moved to BasicLean
