import Game.Metadata
import Game.Generator.Basic

World "EquivalenceRelation"
Level 4

Title "Even and Odd Numbers Form a Partition"

Introduction "A partition of a set X is a collection of nonempty, pairwise disjoint subsets that cover X. The simplest example: every natural number is either even or odd, so {Even} and {Odd} partition the natural numbers. We formalize this using the IsPartition predicate, which requires that the empty set is not in the collection and every element belongs to exactly one member."

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
  Hint "We need to show this is a partition: the empty set is not in the collection, and each natural number belongs to exactly one member. Start by unfolding the definition with `unfold IsPartition`."
  unfold IsPartition
  Hint "Now use `constructor` to split the conjunction."
  constructor
  Hint "The first goal asks that the empty set is not in our collection. Use `exact even_odd_no_empty`."
  exact even_odd_no_empty
  Hint "Now for each natural number a, we must show it belongs to exactly one of Even or Odd. Use `intro a` then `by_cases h : Even a` to split into cases."
  intro a
  by_cases h : Even a
  Hint "In the even case, use `exact even_unique a h`."
  exact even_unique a h
  Hint "In the odd case, use `exact odd_unique a h`."
  exact odd_unique a h

Conclusion "The even and odd natural numbers form a partition. Every partition gives rise to an equivalence relation, and vice versa."

NewTactic by_cases decide push_neg use unfold
