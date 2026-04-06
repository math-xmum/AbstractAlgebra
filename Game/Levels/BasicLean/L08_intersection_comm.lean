import Game.Metadata

World "BasicLean"
Level 8

Title "Intersection is commutative."

Introduction "We prove that set intersection is commutative: $s \\cap t = t \\cap s$. This level introduces three important new tactics: `ext`, `constructor`, and `rintro`.

  **`ext x`** -- When your goal is an equality between two sets, `ext x` reduces it to showing that an arbitrary element `x` belongs to one set if and only if it belongs to the other. (More generally, `ext` proves equality of structures by checking them component-wise.)

  **`constructor`** -- When your goal is a bi-implication `P \\leftrightarrow Q` (or a conjunction `P \\wedge Q`), `constructor` splits it into two separate goals: one for each direction (or each component).

  **`rintro`** -- A powerful introduction tactic that can destructure hypotheses as it introduces them. For example, `rintro \\langle h1, h2\\rangle` introduces a conjunction and immediately names both parts. The syntax `rintro (h | h)` introduces a disjunction and creates one goal per case."

Statement {α : Type*} (s t : Set α): s ∩ t = t ∩ s := by
  Hint "The goal is `s ∩ t = t ∩ s`, an equality of sets. To prove two sets are equal, we show they have the same elements. The `ext x` tactic does exactly this: it introduces an arbitrary element `x` and changes the goal to `x ∈ s ∩ t ↔ x ∈ t ∩ s`.

  Try `ext x`."
  ext x
  Hint "Now unfold the definition of intersection on the left-hand side using `rw [Set.mem_inter_iff]`. This turns the goal into `x ∈ s ∧ x ∈ t ↔ x ∈ t ∩ s`."
  rw [Set.mem_inter_iff]
  Hint "The goal is now a bi-implication (`↔`). The `constructor` tactic splits it into two goals: the forward direction and the backward direction.

  Try `constructor`."
  constructor
  Hint "**Forward direction**: We need to show `x ∈ s ∧ x ∈ t → x ∈ t ∩ s`. Use `rintro ⟨xs, xt⟩` to introduce the hypothesis and simultaneously destructure the conjunction into two parts: `xs : x ∈ s` and `xt : x ∈ t`. Then `exact ⟨xt, xs⟩` closes the goal by providing the pair in swapped order."
  · rintro ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  Hint "**Backward direction**: The same idea applies. Use `rintro ⟨xt, xs⟩` to destructure `x ∈ t ∧ x ∈ s`, then `exact ⟨xs, xt⟩` to provide the pair in the required order."
  · rintro ⟨xt, xs⟩
    exact ⟨xs, xt⟩



Conclusion "You have proved that intersection is commutative using `ext`, `constructor`, and `rintro`. These three tactics form a powerful toolkit: `ext` reduces set equality to element-wise reasoning, `constructor` splits logical connectives, and `rintro` introduces and destructures hypotheses in one step."
NewTactic ext rintro constructor
