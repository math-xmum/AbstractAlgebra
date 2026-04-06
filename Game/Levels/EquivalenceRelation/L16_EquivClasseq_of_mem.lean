import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 16

Introduction "An element `x` belongs to an equivalence class `c` if and only if `c` equals `Setoid.quot x`. In other words, you can identify the class by any of its members. This is the key property that makes equivalence classes well-defined: if `x ∈ c`, then `c` is exactly the equivalence class of `x`."

variable {α :Type*} [inst: Setoid α]

Statement {x : α} {c : Setoid.Equivclass α}  : x ∈ c ↔ c = Setoid.quot x:= by
  Hint "Start by writing `c` as `Setoid.quot y` for some `y`. Use `obtain ⟨y, hy⟩ := Setoid.exist_quot c`."
  obtain ⟨y, hy⟩ := Setoid.exist_quot c
  Hint "Rewrite using `{hy}` so the goal becomes about `Setoid.quot y`. Use `rw [{hy}]`."
  rw [hy]
  Hint "Convert membership to an equivalence using `Setoid.mem_quot_iff_equiv`. Use `rw [Setoid.mem_quot_iff_equiv]`."
  rw [Setoid.mem_quot_iff_equiv]
  Hint "The goal is now `y ≈ x ↔ Setoid.quot y = Setoid.quot x`. The theorem `Setoid.quot_eq_iff_equiv` gives `Setoid.quot y = Setoid.quot x ↔ y ≈ x`, which is the reverse direction. Use `symm` to flip the `↔`, then `exact Setoid.quot_eq_iff_equiv`."
  symm
  exact Setoid.quot_eq_iff_equiv

Conclusion "This result, `Setoid.mem_quot_iff_eq_quot`, says that belonging to a class is the same as the class being your quotient. It will be used frequently in what follows."



OnlyTheorem Setoid.exist_quot Setoid.mem_quot_iff_equiv Setoid.quot_eq_iff_equiv
OnlyTactic rewrite rw rfl obtain  symm exact
