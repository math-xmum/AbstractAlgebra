import Game.Metadata

World "BasicGroupTheory"

Level 15

Introduction "
Left cosets partition the group: any two left cosets of H are either identical or disjoint.

Formally, for any g, k in G, either g • H = k • H or g • H and k • H have empty intersection.

The proof uses the characterization from Level 14: if some element x lies in both cosets, then both z ∈ g • H and z ∈ k • H reduce to the same condition (x⁻¹ * z ∈ H), so the cosets must be equal.
"

open Monoid Group
open scoped Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}

open Pointwise
instance : HSMul G (Set G) (Set G):=inferInstance

Statement  (g k : G) :
  (g • H :Set G) ∩ (k • H : Set G) = ∅ ∨  (g • H :Set G) = (k • H : Set G) := by
  Hint "By classical logic, `P ∨ Q` is equivalent to `\\neg P \\to Q`. The theorem `Classical.or_iff_not_imp_left` encodes this. Use `rw [Classical.or_iff_not_imp_left]` to transform the disjunction into an implication."
  rw [Classical.or_iff_not_imp_left]
  Hint "Introduce the hypothesis that the intersection is nonempty. After `intro hypo` and `push_neg at hypo`, you get an element x in both cosets. Use `obtain` to extract x and its membership proofs."
  intro hypo
  push_neg at hypo
  obtain ⟨x,hx1,hx2⟩ := hypo
  ext z
  Hint "By `Subgroup.mem_coset_iff_diff_mem_subgroup` (from Level 14), since x ∈ g • H, membership z ∈ g • H is equivalent to x⁻¹ * z ∈ H. Use `rw [Subgroup.mem_coset_iff_diff_mem_subgroup hx1]` to rewrite the left side."
  rw [Subgroup.mem_coset_iff_diff_mem_subgroup hx1]
  Hint "Do the same for z ∈ k • H using `hx2`. After rewriting both sides to `x⁻¹ * z ∈ H`, the goal becomes a trivial equality. Note: `rw` automatically closes the goal with `rfl` after rewriting. If you want to see the intermediate state, use the `rewrite` tactic instead, which does not apply `rfl`."
  rewrite [Subgroup.mem_coset_iff_diff_mem_subgroup hx2]
  rfl

NewTheorem Classical.or_iff_not_imp_left Classical.or_iff_not_imp_right Subgroup.mem_coset_iff_diff_mem_subgroup
