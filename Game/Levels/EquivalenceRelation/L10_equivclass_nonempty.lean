import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 10


variable {α :Type*} [inst: Setoid α]

Introduction "
Every equivalence class is **non-empty**: the element $x$ itself always belongs to $[x] = \\{y \\mid x \\approx y\\}$, so this set cannot be $\\emptyset$.

To prove `S ≠ ∅`, a useful strategy is:
1. Use `push_neg` to turn the goal into `∃ x, x ∈ S` (or a similar positive form).
2. Provide a witness with `use`.
3. Simplify membership with `Set.mem_setOf_eq` and close with `rfl`.

The lemma `Set.mem_setOf_eq` rewrites `x ∈ {y | P y}` to `P x`.
"

Statement (x : α) : {y | x ≈ y} ≠ ∅ := by
  Hint "The goal says the equivalence class of `x` is nonempty. Use `push_neg` to rewrite this into a positive existence statement."
  push_neg
  Hint "Now provide `x` itself as the witness: `use x`."
  use x
  Hint "The goal is `x ∈ S` where `S` is the equivalence class of `x`. Use `simp only [Set.mem_setOf_eq]` to unfold the set-builder notation to `x ≈ x`.

`simp only [lemma_name]` is a controlled form of simplification that only applies the listed lemmas."
  simp only [Set.mem_setOf_eq]
  Hint "The goal is `x ≈ x`, which holds by reflexivity. Use `rfl`."
  rfl


NewTheorem Set.mem_setOf_eq
-- NewTactic moved to BasicLean
OnlyTactic push_neg use simp rfl apply rw
