import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 11


variable {α :Type*} [inst: Setoid α]


/-- Equivalence classes with nonempty intersection must be equal. -/
private lemma equivclass_inter_eq {α : Type*} [Setoid α]
    (a b : Set α) (ha : a ∈ Set.range fun (x : α) => {y | x ≈ y})
    (hb : b ∈ Set.range fun (x : α) => {y | x ≈ y})
    (hab : a ∩ b ≠ ∅) : a = b := by
  simp_all
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  push_neg at hab
  obtain ⟨z, haz, hbz⟩ := hab
  rw [← hx] at *
  rw [Setoid.mem_equivclass_iff_equiv] at haz
  rw [← hy] at *
  rw [Setoid.mem_equivclass_iff_equiv] at hbz
  rw [hx, Setoid.equivclass_eq_iff_equiv]
  exact Setoid.trans haz (Setoid.symm hbz)

Statement (preamble := refine ⟨?nonempty , ?union_eq_univ , ?inter_implies_equal⟩ ): IsPartition' <| Set.range fun (x :α) => {y |x ≈ y} := by
  rw [Set.mem_range, not_exists]
  intro x
  simp [Setoid.equivclass_nonempty]
  rw [Set.eq_univ_iff_forall]
  intro x
  simp
  use x
  intro a ha b hb
  exact equivclass_inter_eq a b ha hb


/-
variable {α :Type*} (r : Equivelance α)


Statement (preamble := refine ⟨?nonempty , ?union_eq_univ , ?inter_implies_equal⟩ ): IsPartition' <| Setoid.equivclass '' (Set.univ : Set α)  := by
  simp [Setoid.equivclass_nonempty]
  rw [Set.image_univ, Set.sUnion_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [Set.mem_iUnion]
  use x
  exact Setoid.mem_selfequivclass _
  intro a ha b hb
  obtain ⟨x,_,hx⟩ := ha
  obtain ⟨y,_,hy⟩ := hb
  intro hab
  push_neg at hab
  obtain ⟨z, haz,hbz⟩:= hab
  rw [<-hx] at *
  rw [Setoid.mem_equivclass_iff_equiv] at haz
  rw [<-hy] at *
  rw [Setoid.mem_equivclass_iff_equiv] at hbz
  rw [hx]
  rw [Setoid.equivclass_eq_iff_equiv]
  apply Setoid.trans haz
  exact Setoid.symm hbz
abbrev Equivalence.equivclass : α → Set α := fun x => {y | r x y}
Statement (preamble := constructor): IsPartition <| equivclass r '' Set.univ  := by
-/

NewTheorem Setoid.equivclass_nonempty
