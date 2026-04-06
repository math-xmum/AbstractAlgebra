import Game.Metadata

World "BasicLean"
Level 5

Title "Containing relation is reflexive."

Introduction "This level asks you to prove that every set is a subset of itself -- the reflexivity of the subset relation. Since $s \\subseteq s$ means every element of $s$ is in $s$, the proof is straightforward: introduce an arbitrary element and its membership hypothesis, then use that hypothesis directly."
Statement  {α : Type*} (s : Set α) : s ⊆ s := by
  Hint "The goal is `s ⊆ s`, which unfolds to `∀ x, x ∈ s → x ∈ s`. Use `intro x xs` to introduce an arbitrary element `x` and the hypothesis `xs : x ∈ s`."
  intro x xs
  Hint "The goal is now `x ∈ s`, which is exactly the hypothesis `{xs}`. Use `exact {xs}` to close the goal."
  exact xs

Conclusion "Reflexivity of subset is one of the simplest proofs using `intro` and `exact`. The hypothesis you introduce is exactly what you need to close the goal -- no intermediate steps required."
