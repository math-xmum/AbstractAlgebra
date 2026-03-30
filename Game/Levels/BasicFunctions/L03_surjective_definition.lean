import Game.Metadata

World "BasicFunctions"
Level 3
Title "Definition of surjective function."

Introduction "A function f : α → β is called surjective (or onto) if every element of β is hit by some element of α. In this level you will show that `Function.Surjective f` is definitionally equal to `∀ y, ∃ x, f x = y`."

--#Genhint
Statement {α β γ : Type} (f : α → β) : Function.Surjective f ↔ ∀ y, ∃ x, f x = y := by
  Hint "Since the statement directly matches the definition of surjectivity, you can use `rfl` to complete the proof."
  rfl


Conclusion "Level Completed!"
