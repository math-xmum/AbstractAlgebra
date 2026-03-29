import Game.Metadata

World "BasicLean"
Level 9
Title "Union is associative"

/-- Disjunction is associative: re-bracketing three `Or`s. -/
lemma or_assoc_iff {a b c : Prop} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) := by
  constructor
  · rintro ((h | h) | h)
    · left; exact h
    · right; left; exact h
    · right; right; exact h
  · rintro (h | (h | h))
    · left; left; exact h
    · left; right; exact h
    · right; exact h

Statement {α : Type*} (s t r : Set α): (s ∪ t) ∪ r = s ∪ (t ∪ r) := by
  Hint "We start by showing that the two sets are equal by proving that for every element x, x belongs to both sides of the equation. You can use `ext x`."
  ext x
  Hint "Now we need to rewrite the membership conditions using `Set.mem_union` to express everything in terms of `∨`. Try `rw [Set.mem_union, Set.mem_union, Set.mem_union, Set.mem_union]`."
  rw [Set.mem_union, Set.mem_union, Set.mem_union, Set.mem_union]
  Hint "The goal is now `(x ∈ s ∨ x ∈ t) ∨ x ∈ r ↔ x ∈ s ∨ (x ∈ t ∨ x ∈ r)`. This is just associativity of `∨`. Use `exact or_assoc_iff`."
  exact or_assoc_iff



Conclusion "Level Completed!"
NewTactic left right
