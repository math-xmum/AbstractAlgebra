import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 17

Introduction "Two equivalence classes `Setoid.quot x` and `Setoid.quot y` are equal if and only if `x ≈ y`. This is the fundamental connection between the quotient map and the equivalence relation: the quotient map `Setoid.quot` is injective up to equivalence.

We already proved a version for raw sets (`Setoid.equivclass_eq_iff_equiv`). Here we lift it to the bundled type `Setoid.Equivclass α`."

variable {α :Type*} [inst: Setoid α]

Statement {x y: α} : Setoid.quot x = Setoid.quot y ↔ x ≈ y := by
  Hint "The theorem `Setoid.equivclass_eq_iff_equiv` states that the equivalence class of `x` equals the equivalence class of `y` if and only if `x ≈ y`, for raw sets. Since `Setoid.quot` wraps these sets, we can use `simp [Setoid.equivclass_eq_iff_equiv (α := α)]` to reduce the bundled equality to the raw set equality and close the goal."
  exact Setoid.quot_eq_iff_equiv

Conclusion "This result, `Setoid.quot_eq_iff_equiv`, will be used throughout the remaining levels."



NewTheorem Setoid.equivclass_eq_iff_equiv
OnlyTheorem Setoid.equivclass_eq_iff_equiv
OnlyTactic simp rw
