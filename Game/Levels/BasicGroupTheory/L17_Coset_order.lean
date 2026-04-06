import Game.Metadata

World "BasicGroupTheory"

Level 17

Introduction "
We proved in Level 15 that two left cosets are either equal or disjoint. Let us practice this argument again.

Recall the key tool: `Subgroup.mem_coset_iff_diff_mem_subgroup` tells us that if x ∈ g • H, then for any z, z ∈ g • H is equivalent to x⁻¹ * z ∈ H. This means coset membership depends only on the \"difference\" between elements, not on the representative.

Prove once more that g • H and k • H are either disjoint or equal.
"

open Monoid Group
open scoped Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}

open Pointwise

Statement  (g k : G) :
  (g • H :Set G) ∩ (k • H : Set G) = ∅ ∨  (g • H :Set G) = (k • H : Set G) := by
  Hint "The goal is a disjunction. By classical logic, `P \\lor Q` is equivalent to `\\neg P \\to Q`. Use `rw [Classical.or_iff_not_imp_left]` to convert the goal into an implication."
  rw [Classical.or_iff_not_imp_left]
  Hint "Introduce the hypothesis that the intersection is nonempty. After `intro hypo` and `push_neg at hypo`, extract a common element x with `obtain`."
  intro hypo
  push_neg at hypo
  obtain ⟨x,hx1,hx2⟩ := hypo
  ext z
  Hint "Since x ∈ g • H, `Subgroup.mem_coset_iff_diff_mem_subgroup hx1` lets us rewrite z ∈ g • H as x⁻¹ * z ∈ H."
  rw [Subgroup.mem_coset_iff_diff_mem_subgroup hx1]
  Hint "Similarly rewrite z ∈ k • H using `hx2`. Both sides become x⁻¹ * z ∈ H, and the goal closes by `rfl`. Use `rewrite` instead of `rw` if you want to see the intermediate state before `rfl` is applied automatically."
  rewrite [Subgroup.mem_coset_iff_diff_mem_subgroup hx2]
  rfl

NewTheorem Classical.or_iff_not_imp_left Classical.or_iff_not_imp_right Subgroup.mem_coset_iff_diff_mem_subgroup
