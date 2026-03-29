import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

theorem Set.ne_empty_of_mem {a : α} {s : Set α} (h : a ∈ s) : s ≠ ∅ := fun e =>
  absurd (e ▸ h) (Set.mem_empty_iff_false a).mp


World "EquivalenceRelation"

Level 4

variable {α : Type*} (C : Set (Set α))


private lemma isPartition_imp_isPartition' : IsPartition C → IsPartition' C := by
  unfold IsPartition IsPartition'
  rintro ⟨h1, H2⟩
  refine ⟨h1, ?_, ?_⟩
  · rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_sUnion]
    obtain ⟨t, ht, _⟩ := H2 x
    exact ⟨t, ht⟩
  · intro a ha b hb hab
    push_neg at hab
    obtain ⟨x, hax, hbx⟩ := hab
    have H2x := H2 x
    unfold ExistsUnique at H2x
    obtain ⟨c, _, hc2⟩ := H2x
    have aeqc := hc2 a ⟨ha, hax⟩
    have beqc := hc2 b ⟨hb, hbx⟩
    rw [aeqc, beqc]

private lemma isPartition'_imp_isPartition : IsPartition' C → IsPartition C := by
  unfold IsPartition IsPartition'
  rintro ⟨h1, H1, H2⟩
  refine ⟨h1, ?_⟩
  rw [Set.eq_univ_iff_forall] at H1
  intro x
  obtain ⟨b, hb⟩ := H1 x
  use b
  constructor
  · exact hb
  · intro c hc
    have hcb : c ∩ b ≠ ∅ := Set.ne_empty_of_mem (a := x) ⟨hc.2, hb.2⟩
    exact H2 c hc.1 b hb.1 hcb

Introduction "The following statement shows the equivalence between two definitions of a partition of a set. The first definition (IsPartition) states that a collection $C$ of subsets is a partition if it doesn't contain the empty set and every element belongs to exactly one subset in $C$. The second definition (IsPartition') states that $C$ doesn't contain the empty set, covers the whole space, and its elements are pairwise disjoint."

Statement : IsPartition C ↔ IsPartition' C := by
  Hint "We want to prove an iff statement. We can use the helper lemmas `isPartition_imp_isPartition'` and `isPartition'_imp_isPartition` that break this into two directions. Use `exact Iff.intro (isPartition_imp_isPartition' C) (isPartition'_imp_isPartition C)`."
  exact Iff.intro (isPartition_imp_isPartition' C) (isPartition'_imp_isPartition C)

OnlyTactic intro rfl rw exact simp «have» refine obtain specialize
