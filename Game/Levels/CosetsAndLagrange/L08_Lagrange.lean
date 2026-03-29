import Game.Metadata
import Mathlib.GroupTheory.Coset.Card

World "CosetsAndLagrange"
Level 8
Title "Lagrange's Theorem: Full Statement"

Introduction "The full form of Lagrange's theorem is: |G| = [G:H] · |H|, where [G:H] = |G/H| is the index of H in G (the number of distinct left cosets). This multiplicative formula is the foundation for counting arguments in finite group theory."

variable {G : Type*} [Group G] {H : Subgroup G}

Statement : Nat.card G = Nat.card (G ⧸ H) * Nat.card H := by
  Hint "Use `Subgroup.card_eq_card_quotient_mul_card_subgroup`."
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup H

Conclusion "With Lagrange's theorem in hand, we are ready to study group homomorphisms and quotient groups. Later, the Sylow theorems will give us a partial converse: if p^k divides |G|, then G has a subgroup of order p^k."

NewTheorem Subgroup.card_eq_card_quotient_mul_card_subgroup
