import Game.Metadata
-- import Mathlib

World "CosetsAndLagrange"

Level 4

Title "Coset Transitivity"

Introduction "
Let H be a subgroup of G.

Every left coset g • H is an H-orbit under the right translation action:
Let x ∈ g • H. If y is also in g • H, then there is an element h ∈ H such that x * h = y.  Since `h = x⁻¹ * y`, it means `x⁻¹ * y ∈ H`.
The reverse direction is also true.
We now prove this.

Later we call this
`Subgroup.mem_coset_iff_diff_mem_subgroup`
"

open Monoid Group
open scoped Pointwise
open Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}

private lemma coset_forward {x y : G} (hx : x ∈ g • (H : Set G)) (hy : y ∈ g • (H : Set G)) :
    x⁻¹ * y ∈ H := by
  replace hx := (mem_leftCoset_iff _).1 hx
  replace hy := (mem_leftCoset_iff _).1 hy
  have hxy : x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group
  rw [hxy]
  exact Subgroup.mem_of_inv_mul_mem hx hy

private lemma coset_backward {x y : G} (hx : x ∈ g • (H : Set G)) (hxy : x⁻¹ * y ∈ H) :
    y ∈ g • (H : Set G) := by
  have hgx : g⁻¹ * x ∈ H := (mem_leftCoset_iff _).1 hx
  use (g⁻¹ * x) * (x⁻¹ * y)
  exact ⟨Subgroup.mul_mem _ hgx hxy, by simp; group⟩

Statement {x y : G} (hx : x ∈ g • (H : Set G)) :  y ∈  g • (H : Set G) ↔  x⁻¹ * y ∈ H := by
  Hint "Use `constructor` to split the goals. "
  constructor
  · intro hy
    Hint "Use `mem_leftCoset_iff` to translate
    x ∈ g • H into g⁻¹ x ∈ H. "
    Hint "Note that x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y).
    You can use `have
    have hxy :x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group` to establish this claim.
    "
    Hint "If `a ∈ H`, `b ∈ H`, then `a⁻¹ * b ∈ H`. This is Subgroup.mem_of_inv_mul_mem"
    exact coset_forward hx hy
  · Hint " Since x ∈ g • H, we have g⁻¹ x ∈ H.
    Therefore, that `y = x * (x⁻¹ * y) = g * ((g⁻¹ * x) * (x⁻¹ * y)) ` for some h∈H.  "
    Hint "We start to execute the above argument with `intro hxy`."
    intro hxy
    Hint "Now use `mem_leftCoset_iff` to translate {hx} into g⁻¹ * x ∈ H."
    Hint "Now use ((g⁻¹*x) * (x⁻¹ *y)) to close the goal. "
    exact coset_backward hx hxy

Conclusion "You showed that y ∈ gH if and only if x⁻¹y ∈ H, for any x already in gH. This means each coset is an orbit under right translation by H."
