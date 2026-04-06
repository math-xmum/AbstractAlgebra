import Game.Metadata

World "BasicLean"
Level 7

Title "Definition of union."

Introduction "The union $s \\cup t$ consists of all elements that belong to $s$ or to $t$ (or both). Here we prove that $x \\in s \\cup t$ is equivalent to $x \\in s \\vee x \\in t$, which is the definition of union."
Statement {α : Type*} (s t : Set α) (x : α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  Hint "The goal is $x \\in s \\cup t \\leftrightarrow x \\in s \\vee x \\in t$. Just as with intersection, this is true by definition. Use `rw [Set.mem_union]` to unfold the definition of union on the left-hand side, making both sides identical.

  As before, `rfl` also works since the two sides are definitionally equal."
  rw [Set.mem_union]


Conclusion "You now know the definitional lemmas for both intersection (`Set.mem_inter_iff`) and union (`Set.mem_union`). These will be essential building blocks in the levels ahead."
NewTheorem Set.mem_union
