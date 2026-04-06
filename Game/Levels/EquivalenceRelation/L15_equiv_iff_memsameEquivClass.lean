import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 15

Introduction "If `x` belongs to an equivalence class `c`, then `x ≈ y` if and only if `y` also belongs to `c`. This captures the key idea that equivalence classes group together all mutually equivalent elements.

The proof strategy is: express `c` as `Setoid.quot z` for some `z`, convert memberships to equivalences via `Setoid.mem_quot_iff_equiv`, and then use transitivity properties."

variable {α :Type*} [inst: Setoid α]


Statement {c : Setoid.Equivclass α} {x y : α}  (H : x ∈ c) :  x ≈ y  ↔  y ∈ c  := by
  Hint "First, express `c` as `Setoid.quot z` for some `z`. Use `obtain ⟨z, hz⟩ := Setoid.exist_quot c`. The theorem `Setoid.exist_quot` says every equivalence class has a representative."
  obtain ⟨z,hz⟩:= Setoid.exist_quot c
  Hint "Now rewrite the hypothesis `H : x ∈ c` using `{hz} : c = Setoid.quot z`. Use `rw [{hz}] at H`."
  rw [hz] at H
  Hint "Also rewrite the goal so `c` becomes `Setoid.quot z`. Use `rw [{hz}]`."
  rw [hz]
  Hint "Convert the membership `x ∈ Setoid.quot z` to the equivalence `z ≈ x` using `rw [Setoid.mem_quot_iff_equiv] at H`."
  rw [Setoid.mem_quot_iff_equiv] at H
  Hint "Similarly, convert the goal's membership to an equivalence. Use `rw [Setoid.mem_quot_iff_equiv]`."
  rw [Setoid.mem_quot_iff_equiv]
  Hint "We now have `H : z ≈ x` and need `x ≈ y ↔ z ≈ y`. Apply symmetry to get `x ≈ z`. Use `replace H := Setoid.symm H`. The `replace` tactic works like `have` but replaces the existing hypothesis."
  replace H := Setoid.symm H
  Hint "The goal `x ≈ y ↔ z ≈ y` follows from `Setoid.equiv_iff_of_equiv`, which says if `x ≈ z` then `(x ≈ y ↔ z ≈ y)`. Use `exact Setoid.equiv_iff_of_equiv H`."
  exact Setoid.equiv_iff_of_equiv H

Conclusion "This is a central property: membership in an equivalence class is stable under the equivalence relation."



NewTheorem Setoid.exist_quot
OnlyTactic rewrite rfl rw obtain «have» replace exact
OnlyTheorem Setoid.exist_quot Setoid.mem_quot_iff_equiv Setoid.equiv_iff_of_equiv Setoid.symm
