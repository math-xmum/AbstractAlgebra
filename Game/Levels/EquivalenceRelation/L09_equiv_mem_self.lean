import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 9


variable {α :Type*} [inst: Setoid α]


Introduction "
The **equivalence class** of an element $x$ under a setoid is the set $[x] = \\{y \\mid x \\approx y\\}$. In Lean, this is written as `{y | x ≈ y}`.

A basic but important fact: every element belongs to its own equivalence class. This follows directly from reflexivity of `≈`.

The lemma `Setoid.refl` states `∀ x, x ≈ x`. The underscore `_` in `Setoid.refl _` asks Lean to infer the argument automatically.
"

Statement
 (x : α) : x ∈ {y | x ≈ y} := by
  Hint "The goal is `x ∈ S` where `S` is the equivalence class of `x`, which unfolds to `x ≈ x`. This is exactly reflexivity. Use `exact Setoid.refl _`.

Here `_` tells Lean to figure out the argument (which is `x`) from context."
  exact Setoid.refl _


NewTheorem Setoid.refl
OnlyTactic rewrite unfold exact
