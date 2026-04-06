import Game.Metadata

World "BasicLean"
Level 10
Title "Exercise"

Introduction "We prove that if $s \\subseteq t$, then $s \\cap t = s$. Intuitively, intersecting a set with a superset does not remove any elements, so the result is just $s$ itself. This exercise combines the techniques from previous levels: `ext`, `constructor`, `rw`, and function-style terms like `fun ha \\mapsto ...`."
Statement  {α : Type*} (s t : Set α) : s ⊆ t → s ∩ t =  s  := by
  Hint "The goal starts with an implication `s ⊆ t → ...`. Use `intro h` to move the hypothesis into context as `h : s ⊆ t`."
  intro h
  Hint "To prove the set equality `s ∩ t = s`, use `ext x` to reduce it to showing `x ∈ s ∩ t ↔ x ∈ s` for an arbitrary `x`."
  ext x
  Hint "Unfold the intersection definition with `rw [Set.mem_inter_iff]`. The goal becomes `x ∈ s ∧ x ∈ t ↔ x ∈ s`."
  rw [Set.mem_inter_iff]
  Hint "Split the bi-implication into two goals with `constructor`."
  constructor
  Hint "**Forward direction** (`x ∈ s ∧ x ∈ t → x ∈ s`): We just need the first component of the conjunction. The term `fun ha ↦ ha.1` is a function that takes a proof `ha` of `x ∈ s ∧ x ∈ t` and returns its first component `ha.1 : x ∈ s`. Use `exact fun ha ↦ ha.1`."
  exact fun ha ↦ ha.1
  Hint "**Backward direction** (`x ∈ s → x ∈ s ∧ x ∈ t`): Given `ha : x ∈ s`, we need both `x ∈ s` (which is `ha`) and `x ∈ t` (which follows from `h : s ⊆ t` applied to `ha`, i.e., `h ha`). The term `⟨ha, h ha⟩` constructs this pair. Use `exact fun ha ↦ ⟨ha, h ha⟩`."
  exact fun ha ↦ ⟨ha, h ha⟩



Conclusion "Well done! You combined set extensionality, rewriting, and term-mode proofs to show that intersecting with a superset is the identity. Notice how `h ha` applies the subset hypothesis like a function -- in Lean, `s ⊆ t` is definitionally `∀ x, x ∈ s → x ∈ t`, so `h` is a function from membership proofs to membership proofs."

NewTactic pick_goal «have» «repeat» replace aesop simp_all specialize trivial «let» norm_cast unfold decide native_decide
simp simp_rw linarith assumption push_neg rewrite use rcases obtain «suffices» by_cases exfalso refine omega nth_rw group apply_fun beta_reduce
