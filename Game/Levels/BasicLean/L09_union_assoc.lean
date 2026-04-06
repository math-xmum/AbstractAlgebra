import Game.Metadata

World "BasicLean"
Level 9
Title "Union is associative"

Introduction "We prove that set union is associative: $(s \\cup t) \\cup r = s \\cup (t \\cup r)$. This level introduces two new tactics for working with disjunctions (\"or\" statements):

  **`left`** -- When your goal is a disjunction `P \\vee Q`, the `left` tactic changes the goal to `P`. You are committing to proving the left alternative.

  **`right`** -- Similarly, `right` changes a goal `P \\vee Q` to `Q`, committing to the right alternative.

  Since set union corresponds to logical disjunction, these tactics are essential for proving union-related statements."

Statement {α : Type*} (s t r : Set α): (s ∪ t) ∪ r = s ∪ (t ∪ r) := by
  Hint "As in the previous level, we prove set equality by showing both sides have the same elements. Use `ext x` to introduce an arbitrary element `x`."
  ext x
  Hint "Unfold one layer of union using `rw [Set.mem_union]`. This rewrites the outermost union on the left-hand side of the `↔`."
  rw [Set.mem_union]
  Hint "The goal is a bi-implication. Use `constructor` to split it into two directions."
  constructor
  Hint "**Forward direction**: The hypothesis is a disjunction (`x ∈ s ∪ t ∨ x ∈ r`). Use `rintro (h | h)` to introduce it and case-split: the first case gives `h : x ∈ s ∪ t`, the second gives `h : x ∈ r`."
  rintro (h | h)
  Hint "Unfold the union definition everywhere (in the goal and hypotheses) with `rw [Set.mem_union] at *`."
  rw [Set.mem_union] at *
  Hint "The hypothesis `h : x ∈ s ∨ x ∈ t` is itself a disjunction. Use `rcases h with h | h` to case-split on it."
  rcases h with h | h
  Hint "We have `h : x ∈ s` and need to show `x ∈ s ∨ x ∈ t ∪ r`. Since we can prove the left disjunct, use `left`."
  left
  Hint "The goal is now exactly `h`. Close it with `exact h`."
  exact h
  Hint "We have `h : x ∈ t` and need `x ∈ s ∨ x ∈ t ∪ r`. Use `right` to commit to proving the right disjunct."
  right
  Hint "Unfold the union with `rw [Set.mem_union]`, then use `left` since we know `x ∈ t`."
  rw [Set.mem_union]
  Hint "Use `left` and then `exact h`."
  left
  Hint "Close the goal with `exact h`."
  exact h
  Hint "Now we handle `h : x ∈ r`. We need `x ∈ s ∨ x ∈ t ∪ r`. Use `right`."
  right
  Hint "Unfold the union with `rw [Set.mem_union]`, then use `right` since we know `x ∈ r`."
  rw [Set.mem_union]
  Hint "Use `right` to select the `x ∈ r` disjunct."
  right
  Hint "Close the goal with `exact h`."
  exact h
  Hint "**Backward direction**: Use `rintro (h | h)` to case-split on whether `x ∈ s` or `x ∈ t ∪ r`."
  rintro (h | h)
  Hint "We have `h : x ∈ s` and need `x ∈ s ∪ t ∨ x ∈ r`. Use `left` to focus on `x ∈ s ∪ t`."
  left
  Hint "Unfold with `rw [Set.mem_union]`, then `left` and `exact h`."
  rw [Set.mem_union]
  Hint "Use `left` to pick `x ∈ s`, then `exact h`."
  left
  exact h
  Hint "We have `h : x ∈ t ∪ r`. Case-split with `rcases h with h | h`."
  rcases h with h | h
  Hint "We have `h : x ∈ t`. Use `left` to target `x ∈ s ∪ t`."
  left
  Hint "Unfold with `rw [Set.mem_union]`, then `right` and `exact h`."
  rw [Set.mem_union]
  Hint "Use `right` to pick `x ∈ t`, then `exact h`."
  right
  exact h
  Hint "We have `h : x ∈ r` and need `x ∈ s ∪ t ∨ x ∈ r`. Use `right`."
  right
  Hint "Close the goal with `exact h`."
  exact h



Conclusion "You proved associativity of union! The `left` and `right` tactics let you choose which side of a disjunction to prove. Combined with `rintro (h | h)` for case-splitting on disjunctions, you now have all the tools needed to reason about union membership."
NewTactic left right
