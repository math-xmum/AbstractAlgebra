import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 15


variable {α :Type*} [inst: Setoid α]


Statement {c : Setoid.Equivclass α} (x y : α) (H : x ∈ c) :  x ≈ y  ↔  y ∈ c  := by
  obtain ⟨z,hz⟩:= Setoid.exist_quot c
  rw [hz] at H
  rw [hz]
  rw [Setoid.mem_quot_iff_equiv] at H
  rw [Setoid.mem_quot_iff_equiv]
  replace H := Setoid.symm H
  exact Setoid.equiv_iff_of_equiv H



NewTheorem Setoid.exist_quot
OnlyTactic rewrite rfl rw obtain «have» replace exact
OnlyTheorem Setoid.exist_quot Setoid.mem_quot_iff_equiv Setoid.equiv_iff_of_equiv Setoid.symm
