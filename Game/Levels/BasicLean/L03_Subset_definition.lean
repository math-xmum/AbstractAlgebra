import Game.Metadata

World "BasicLean"
Level 3

Title "Subset in Lean"

Introduction "
Suppose α is a type. Collection of elements of type α is called a set.
Technically a ``Set α`` is implemented as a function from α to Prop.

If p : α → Prop, then p is called a predicate on α.
Now ``setOf p`` is the set {x : α | p x}.

There are two special subset, one is the empty set $∅$, and the universal set $(univ : Set α)$.

The statement asserts that a set $s$ is a subset of a set $t$ if and only if every element $x$ in $s$ is also in $t$. This is essentially the definition of a subset, which states that for $s \\subseteq t$ to be true, every element of $s$ must also be an element of $t$."

Statement (α : Type*) (s t : Set α): s ⊆ t ↔ ∀ x, x ∈ s → x ∈  t  := by
  Hint "This statement is true by definition. You can simply use `rfl` to indicate that the left-hand side is equal to the right-hand side by definition."
  rfl


Conclusion "Level Completed!"
