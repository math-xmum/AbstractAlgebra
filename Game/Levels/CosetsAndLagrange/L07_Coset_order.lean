import Game.Metadata
import Mathlib.GroupTheory.Coset.Card

World "CosetsAndLagrange"
Level 7
Title "Order of Subgroup Divides Order of Group"

Introduction "Lagrange's theorem states that for a finite group G and a subgroup H, the order of H divides the order of G. This is a direct consequence of the fact that left cosets of H partition G into equal-sized blocks."

variable {G : Type*} [Group G] {H : Subgroup G}

Statement : Nat.card H ∣ Nat.card G := by
  Hint "This is Lagrange's theorem. In Mathlib, it is `Subgroup.card_subgroup_dvd_card`."
  exact Subgroup.card_subgroup_dvd_card H

Conclusion "Lagrange's theorem has many important consequences: the order of every element divides the order of the group, and a group of prime order must be cyclic."

NewTheorem Subgroup.card_subgroup_dvd_card
