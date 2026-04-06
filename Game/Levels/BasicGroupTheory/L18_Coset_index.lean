import Game.Metadata

World "BasicGroupTheory"

Level 18

Introduction "
This is the final practice level for coset disjointness. The collection of all left cosets G/H := {g • H | g ∈ G} forms a partition of G: every element belongs to exactly one coset, and distinct cosets are disjoint.

The number of distinct cosets |G/H| is called the **index** of H in G. Since the cosets partition G and each coset has the same size as H (by the bijection from Level 12), we get **Lagrange's theorem**: |G| = |G/H| * |H|.

Prove once more that any two left cosets are either equal or disjoint.
"

open Monoid Group
open scoped Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}

open Pointwise

Statement  (g k : G) :
  (g • H :Set G) ∩ (k • H : Set G) = ∅ ∨  (g • H :Set G) = (k • H : Set G) := by
  Hint "Convert the disjunction to an implication using `rw [Classical.or_iff_not_imp_left]`. This rewrites `P \\lor Q` as `\\neg P \\to Q`."
  rw [Classical.or_iff_not_imp_left]
  Hint "Assume the intersection is nonempty with `intro hypo`. Then `push_neg at hypo` gives an existential, and `obtain` extracts a witness x in both cosets. Finally `ext z` reduces set equality to pointwise membership."
  intro hypo
  push_neg at hypo
  obtain ⟨x,hx1,hx2⟩ := hypo
  ext z
  Hint "Apply `Subgroup.mem_coset_iff_diff_mem_subgroup` with the proof that x ∈ g • H to rewrite z ∈ g • H as x⁻¹ * z ∈ H."
  rw [Subgroup.mem_coset_iff_diff_mem_subgroup hx1]
  Hint "Do the same for z ∈ k • H. After both rewrites, both sides are x⁻¹ * z ∈ H, so `rfl` (or `rw` which applies `rfl` automatically) closes the goal."
  rewrite [Subgroup.mem_coset_iff_diff_mem_subgroup hx2]
  rfl

NewTheorem Classical.or_iff_not_imp_left Classical.or_iff_not_imp_right Subgroup.mem_coset_iff_diff_mem_subgroup
