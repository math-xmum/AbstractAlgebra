import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 6



#check Odd

private lemma even_odd_no_empty :
    ∅ ∉ ({({x : ℕ | Even x}), {x : ℕ | Odd x}} : Set (Set ℕ)) := by
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  push_neg
  constructor
  · use 0; decide
  · use 1; decide

private lemma even_unique (a : ℕ) (h : Even a) :
    ∃! b, b ∈ ({({x : ℕ | Even x}), {x : ℕ | Odd x}} : Set (Set ℕ)) ∧ a ∈ b := by
  use {x : ℕ | Even x}
  simp
  exact ⟨h, fun ha => by exfalso; obtain ⟨r, hr⟩ := h; obtain ⟨k, hk⟩ := ha; omega⟩

private lemma odd_unique (a : ℕ) (h : ¬ Even a) :
    ∃! b, b ∈ ({({x : ℕ | Even x}), {x : ℕ | Odd x}} : Set (Set ℕ)) ∧ a ∈ b := by
  use {x : ℕ | Odd x}
  simp
  exact ⟨(Nat.even_or_odd a).resolve_left h, fun h' => by exfalso; exact h h'⟩

Statement : IsPartition {{x : ℕ | Even x}, {x : ℕ | Odd x}} := by
  unfold IsPartition
  constructor
  exact even_odd_no_empty
  intro a
  by_cases h : Even a
  exact even_unique a h
  exact odd_unique a h




  --suffices {x:ℕ  | Even x} ∪ {x:ℕ | ¬ Even x} = Set.univ from by simp
  --rw [Set.sUnion_insert, Set.sUnion_singleton]





NewTactic «intro» rfl rw exact simp «have» by_cases simp exfalso by_cases use push_neg decide
OnlyTactic intro rfl rw exact simp «have» by_cases simp exfalso by_cases use push_neg decide
