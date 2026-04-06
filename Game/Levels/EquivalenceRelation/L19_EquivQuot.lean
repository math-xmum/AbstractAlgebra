import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 19

Introduction "`Setoid.quot x = c` if and only if `x ∈ c`. This is the flip side of L16 (which showed `x ∈ c ↔ c = Setoid.quot x`). Here the equality is written with `Setoid.quot x` on the left.

The proof uses `Setoid.mem_quot_iff_equiv'`, which gives `y ∈ Setoid.quot x ↔ y ≈ x` (note the swapped order compared to `mem_quot_iff_equiv`)."

variable {α :Type*} [inst: Setoid α]

variable (c : Setoid.Equivclass α)

Statement (x : α) : Setoid.quot x = c ↔ x ∈ c:= by
  Hint "Express `c` as `Setoid.quot y`. Use `obtain ⟨y, hy⟩ := Setoid.exist_quot c`."
  obtain ⟨y, hy⟩ := Setoid.exist_quot c
  Hint "Rewrite with `{hy}`. Use `rw [{hy}]`."
  rw [hy]
  Hint "Convert the membership on the right to an equivalence. `Setoid.mem_quot_iff_equiv'` gives `x ∈ Setoid.quot y ↔ x ≈ y`. Use `rw [Setoid.mem_quot_iff_equiv']`."
  rw [Setoid.mem_quot_iff_equiv']
  Hint "The goal is now `Setoid.quot x = Setoid.quot y ↔ x ≈ y`, which is exactly `Setoid.quot_eq_iff_equiv`. Use `exact Setoid.quot_eq_iff_equiv`."
  exact Setoid.quot_eq_iff_equiv

Conclusion "We now have both directions: `x ∈ c ↔ c = Setoid.quot x` and `Setoid.quot x = c ↔ x ∈ c`."
