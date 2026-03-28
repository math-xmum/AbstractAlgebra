import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 22


variable {α :Type*} [inst: Setoid α]

variable (c : Setoid.Equivclass α)

--#check c.unquot

Statement (β : Type*) (f : α → β) (H: ∀ a b, a ≈ b → f a = f b):
  let fbar :Setoid.Equivclass α → β := fun c => f c.unquot
  ∀ x, f x = fbar (Setoid.quot x)
  := by
  intro x
  simp [fbar]
  apply H
  exact Setoid.unquot_quot_equiv

NewTheorem Setoid.unquot_quot_equiv
