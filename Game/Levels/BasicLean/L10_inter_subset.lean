import Game.Metadata

World "BasicLean"
Level 10
Title "Exercise"

Introduction "The following statement claims that if a set $s$ is a subset of a set $t$, then the intersection of $s$ and $t$ is equal to $s$.
This is essentially stating that taking the intersection of a set with a superset yields the original set."
Statement  {α : Type*} (s t : Set α) : s ⊆ t → s ∩ t =  s  := by
  Hint "We start by introducing the hypothesis h that {s} ⊆ {t}. You can use `intro h`."
  intro h
  Hint "To prove set equality, we need to show that an arbitrary element x is in both sets if and only if it's in the other. You can use `ext x` to start this process."
  ext x
  Hint "The goal is now to show {x} ∈ {s} ∧ {x} ∈ {t} ↔ {x} ∈ {s}. Use `rw [Set.mem_inter_iff]` to rewrite the goal using the definition of set intersection."
  rw [Set.mem_inter_iff]
  Hint "To prove the equivalence, we need to show both directions: {x} ∈ {s} ∧ {x} ∈ {t} → {x} ∈ {s}, and {x} ∈ {s} → {x} ∈ {s} ∧ {x} ∈ {t}. Use `constructor` to split the goal into two parts."
  constructor
  Hint "For the left direction, we need to show {x} ∈ {s} ∧ {x} ∈ {t} → {x} ∈ {s}. This is straightforward since {x} ∈ {s} already holds in the hypothesis. Use `exact fun ha ↦ ha.1`."
  exact fun ha ↦ ha.1
  Hint "For the right direction, we need to show {x} ∈ {s} → {x} ∈ {s} ∧ {x} ∈ {t}. Use the fact that {h} gives us {x} ∈ {t} whenever {x} ∈ {s}. Use `exact fun ha ↦ ⟨ha, h ha⟩`."
  exact fun ha ↦ ⟨ha, h ha⟩



Conclusion "Level Completed!"

NewTactic pick_goal «have» «repeat» replace aesop simp_all specialize trivial «let» norm_cast unfold decide native_decide
simp simp_rw linarith assumption push_neg rewrite use by_cases
