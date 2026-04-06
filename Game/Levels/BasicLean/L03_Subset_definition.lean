import Game.Metadata

World "BasicLean"
Level 3

Title "Subset in Lean"

Introduction "In Lean, given a type `α`, a `Set α` is a collection of elements of type `α`. Technically, `Set α` is implemented as a function `α → Prop` -- a predicate that says which elements belong to the set. Given a predicate `p : α → Prop`, the expression `setOf p` denotes the set `{x : α | p x}`.

Two important special sets are the empty set `∅` (no elements) and the universal set `univ : Set α` (all elements of `α`).

In this level, you will prove that `s ⊆ t` if and only if every element of `s` is also an element of `t`. This is simply the *definition* of the subset relation, so it holds by definitional equality."

Statement (α : Type*) (s t : Set α): s ⊆ t ↔ ∀ x, x ∈ s → x ∈  t  := by
  Hint "The two sides of the `↔` are definitionally equal: `s ⊆ t` *means* `∀ x, x ∈ s → x ∈ t` by definition. Since both sides are the same by definition, `rfl` closes the goal."
  rfl


Conclusion "The key insight is that `s ⊆ t` is *defined* as `∀ x, x ∈ s → x ∈ t` in Lean, so `rfl` recognizes them as the same thing. Definitional equality is a powerful concept -- when two expressions reduce to the same thing by unfolding definitions, `rfl` can close the goal without any further reasoning."
