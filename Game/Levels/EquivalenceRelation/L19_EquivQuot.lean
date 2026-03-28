import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 19


variable {α :Type*} [inst: Setoid α]

variable (c : Setoid.Equivclass α)

Statement (x : α) : Setoid.quot x = c ↔ x ∈ c:= by
  obtain ⟨y, hy⟩ := Setoid.exist_quot c
  rw [hy]
  rw [Setoid.mem_quot_iff_equiv']
  exact Setoid.quot_eq_iff_equiv
