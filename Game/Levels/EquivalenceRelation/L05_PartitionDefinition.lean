import Game.Metadata
import Game.Generator.Basic

World "EquivalenceRelation"
Level 5

Title "Two Definitions of Partition"

variable {α : Type*} (C : Set (Set α))

theorem Set.ne_empty_of_mem {a : α} {s : Set α} (h : a ∈ s) : s ≠ ∅ := fun e =>
  absurd (e ▸ h) (Set.mem_empty_iff_false a).mp

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

Introduction "There are two natural ways to define a partition of a set. The first (IsPartition) says that the empty set is not in the collection and every element belongs to a unique member. The second (IsPartition') says that the empty set is not in the collection, the union of all members is the whole set, and distinct members are disjoint. These two definitions are equivalent, and we prove this using two helper lemmas."

Statement : IsPartition C ↔ IsPartition' C := by
  Hint "The proof is assembled from two helper lemmas, one for each direction. Use `exact Iff.intro (isPartition_imp_isPartition' C) (isPartition'_imp_isPartition C)`."
  exact Iff.intro (isPartition_imp_isPartition' C) (isPartition'_imp_isPartition C)

Conclusion "We have shown the two definitions of partition are equivalent. This level teaches that complex proofs can be broken into helper lemmas and then assembled at the end."

NewTactic intro rfl rw exact simp «have»
