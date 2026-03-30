import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 10

Title "Equivalence Classes Form a Partition"

Introduction "This is the key theorem connecting equivalence relations to partitions: the collection of all equivalence classes of ≈ forms a partition of α. Each element belongs to exactly one equivalence class, the classes are nonempty, and distinct classes are disjoint."

variable {α : Type*} [Setoid α]

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

private lemma equivclass_partition (α : Type*) [Setoid α] :
    IsPartition' (Set.range fun (x : α) => {y | x ≈ y}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.mem_range, not_exists]
    intro x
    simp [Setoid.equivclass_nonempty]
  · rw [Set.eq_univ_iff_forall]
    intro x; simp; use x
  · intro a ha b hb
    exact equivclass_inter_eq a b ha hb

Statement : IsPartition' (Set.range fun (x : α) => {y | x ≈ y}) := by
  Hint "This is the key theorem: equivalence classes form a partition. The proof has three parts (nonempty, union covers all, pairwise disjoint). We have prepared the lemma `equivclass_partition` which proves all three. Use `exact equivclass_partition α`."
  exact equivclass_partition α

Conclusion "This is one of the central results about equivalence relations: they give rise to partitions. Conversely, every partition defines an equivalence relation."

NewTheorem Setoid.equivclass_nonempty
OnlyTactic rw intro simp use exact obtain push_neg constructor
