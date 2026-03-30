import Game.Metadata

World "BasicLean"
Level 3

Title "Subset in Lean"

Introduction "The statement asserts that a set $s$ is a subset of a set $t$ if and only if every element $x$ in $s$ is also in $t$. This is essentially the definition of a subset, which states that for $s \\subseteq t$ to be true, every element of $s$ must also be an element of $t$."

Statement {α : Type*} (s t : Set α): s ⊆ t ↔ ∀ x, x ∈ s → x ∈  t  := by
  Hint "This statement is true by definition. You can simply use `rfl` to indicate that the left-hand side is equal to the right-hand side by definition."
  rfl


Conclusion "Level Completed!"

NewDefinition Set Set.mem_setOf_eq
