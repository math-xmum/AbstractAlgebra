import Game.Metadata

World "BasicFunctions"
Level 5
Title "Definition of bijective function."

Introduction "The following statement claims that a function $f$ is bijective if and only if it is both injective and surjective. This is a fundamental characterization of bijective functions in mathematics, connecting the global property of bijectivity with the combination of injectivity and surjectivity."

Statement {α β : Type} (f : α → β) : Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f := by
  Hint "This is a definitional equality in Lean, meaning the left-hand side (Bijective) is defined to be exactly the right-hand side (Injective ∧ Surjective). Therefore, we can prove it immediately using reflexivity (`rfl`)."
  rfl

Conclusion "Level Completed!"
NewTactic use rfl constructor
