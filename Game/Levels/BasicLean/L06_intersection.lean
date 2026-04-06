import Game.Metadata

World "BasicLean"
Level 6

Title "Definition of intersection."

Introduction "In set theory, the intersection $s \\cap t$ consists of all elements that belong to both $s$ and $t$. Here we prove that $x \\in s \\cap t$ is equivalent to $x \\in s \\wedge x \\in t$, which is essentially the definition of intersection."

Statement  {α : Type*} (s t : Set α) (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈  t  := by
  Hint "The goal is to show that $x \\in s \\cap t \\leftrightarrow x \\in s \\wedge x \\in t$. Since this is true by the definition of set intersection, we can unfold that definition using `rw [Set.mem_inter_iff]`. This rewrites the left-hand side so both sides become identical, and the goal is closed automatically.

  Alternatively, `rfl` also works here, because the two sides are *definitionally* equal."
  rw [Set.mem_inter_iff]

Conclusion "Well done! You used the theorem `Set.mem_inter_iff` to unfold the definition of set intersection. This pattern of rewriting with a definitional lemma will appear often."
NewTheorem Set.mem_inter_iff
