import Game.Metadata

World "CosetsAndLagrange"

Level 5

Introduction "
Let H be a subgroup of G.
For two cosets g • H and k • H, either
g • H ∩ k • H = ∅  or g • H = k • H.

We now prove this statement.
"

open Monoid Group
open scoped Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}

open Pointwise
instance : HSMul G (Set G) (Set G):=inferInstance

Statement  (g k : G) :
  (g • H :Set G) ∩ (k • H : Set G) = ∅ ∨  (g • H :Set G) = (k • H : Set G) := by
  Hint "By classical logic, P ∨ Q is equivalent to ¬ P → Q.
  Rewrite using `Classical.or_iff_not_imp_left` to translate the goal into ¬ P → Q. "
  rw [Classical.or_iff_not_imp_left]
  Hint "Now introduce a hypothesis `hypo : ¬ (g • H :Set G) = (k • H : Set G)`"
  intro hypo
  push_neg at hypo
  obtain ⟨x,hx1,hx2⟩ := hypo
  ext z
  Hint "By `Subgroup.mem_coset_iff_diff_mem_subgroup`, z ∈ g • H ↔ z⁻¹ * x ∈ H. One can use rewrite to replace z ∈ g • H with z⁻¹ * x ∈ H. "
  rw [Subgroup.mem_coset_iff_diff_mem_subgroup hx1]
  Hint "Do the same thing for z ∈ k • H. If you use `rw` The goal is automatically closed since `rw` all rewrite the goal and then apply `rfl`. If you wish to prevent this, you can use the tactic `rewrite` instead."
  rewrite [Subgroup.mem_coset_iff_diff_mem_subgroup hx2]
  rfl

NewTheorem Classical.or_iff_not_imp_left Classical.or_iff_not_imp_right Subgroup.mem_coset_iff_diff_mem_subgroup
