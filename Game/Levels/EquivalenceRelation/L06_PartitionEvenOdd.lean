import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 6



#check Odd

Introduction "
A concrete example: the natural numbers $\\mathbb{N}$ can be partitioned into **even** and **odd** numbers. The collection $C = \\{\\{x \\mid \\text{Even}\\; x\\},\\; \\{x \\mid \\text{Odd}\\; x\\}\\}$ satisfies `IsPartition C`.

We must show: (1) neither set is empty, and (2) every natural number belongs to exactly one of them. This is a longer, more computational proof that uses several new tactics:

- `by_cases h : P` -- splits into two subgoals: one where `P` holds and one where `¬P` holds.
- `refine ⟨..., ?_⟩` -- partially fills a goal, leaving `?_` as a placeholder for what remains.
- `rcases h with rfl | rfl` -- case-splits a disjunction and substitutes equalities.
- `exfalso` -- changes the goal to `False`, useful for deriving a contradiction.
- `decide` -- solves decidable propositions by computation.
- `omega` -- solves linear arithmetic goals over natural numbers and integers.
"

Statement : IsPartition {{x : ℕ | Even x}, {x : ℕ | Odd x}} := by
  Hint "Start by unfolding the definition: `unfold IsPartition`. Then use `constructor` to split into the two conditions."
  unfold IsPartition
  Hint (hidden := true) "Use `constructor`."
  constructor
  Hint "We need to show $\\emptyset$ is neither the even set nor the odd set. Rewrite set membership with `rw [Set.mem_insert_iff, Set.mem_singleton_iff]`, then use `push_neg` to distribute the negation."
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  Hint (hidden := true) "Use `push_neg` then `constructor`."
  push_neg
  Hint (hidden := true) "Use `constructor` to split into two subgoals."
  constructor
  Hint "To show the even set is non-empty, provide a witness: `use 0; decide`. The `decide` tactic evaluates decidable propositions."
  use 0; decide
  Hint "Similarly for the odd set: `use 1; decide`."
  use 1; decide
  Hint "Now for each natural number `a`, we show it belongs to exactly one set. Use `intro a`, then `by_cases h : Even a` to split on parity.

The `by_cases` tactic performs case analysis on a decidable proposition."
  intro a
  Hint (hidden := true) "Use `by_cases h : Even a`."
  by_cases h : Even a
  Hint "**Case: `a` is even.** Provide the even set as witness. Use the set of even natural numbers."
  use {x : ℕ | Even x}
  Hint "Use `refine ⟨⟨Set.mem_insert _ _, h⟩, ?_⟩` to fill in what we know and leave uniqueness as a subgoal.

The `refine` tactic is like `exact` but allows holes marked with `?_`."
  refine ⟨⟨Set.mem_insert _ _, h⟩, ?_⟩
  Hint "For uniqueness, introduce another set `y` containing `a`: `intro y ⟨hy_mem, hy_a⟩`."
  intro y ⟨hy_mem, hy_a⟩
  Hint "Rewrite `hy_mem` to see which set `y` is: `rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem`."
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
  Hint "Case-split on whether `y` is the even or odd set: `rcases hy_mem with rfl | rfl`.

The `rcases` tactic destructs hypotheses recursively. The pattern `rfl` substitutes an equality immediately."
  rcases hy_mem with rfl | rfl
  · rfl
  · exfalso; obtain ⟨k1, hk1⟩ := h; obtain ⟨k2, hk2⟩ := hy_a; omega
  Hint "**Case: `a` is not even (so odd).** Provide the odd set as witness."
  use {x : ℕ | Odd x}
  Hint (hidden := true) "Use `refine` to fill in the membership proof and leave uniqueness."
  refine ⟨⟨Set.mem_insert_of_mem _ rfl, Nat.not_even_iff_odd.mp h⟩, ?_⟩
  Hint (hidden := true) "Introduce another set and case-split as before."
  intro y ⟨hy_mem, hy_a⟩
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem
  rcases hy_mem with rfl | rfl
  · exfalso; exact h hy_a
  · rfl




  --suffices {x:ℕ  | Even x} ∪ {x:ℕ | ¬ Even x} = Set.univ from by simp
  --rw [Set.sUnion_insert, Set.sUnion_singleton]





-- NewTactic moved to BasicLean
OnlyTactic intro rfl rw exact simp «have» by_cases simp exfalso by_cases use push_neg decide refine rcases obtain omega
