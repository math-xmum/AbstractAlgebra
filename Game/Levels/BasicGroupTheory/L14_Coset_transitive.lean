import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 14

Introduction "
Two elements x and y belong to the same left coset g • H if and only if x⁻¹ * y ∈ H.

Intuitively, if x = g * h₁ and y = g * h₂ for h₁, h₂ ∈ H, then x⁻¹ * y = h₁⁻¹ * h₂ ∈ H. The converse also holds.

This characterization is very useful: it lets us test coset membership without referring to the coset representative g. We prove it here and call it `Subgroup.mem_coset_iff_diff_mem_subgroup` in later levels.
"

open Monoid Group
open scoped Pointwise
open Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}


Statement {x y : G} (hx : x ∈ g • (H : Set G)) :  y ∈  g • (H : Set G) ↔  x⁻¹ * y ∈ H := by
  Hint "This is a biconditional (iff). Use `constructor` to split it into two implications."
  constructor
  · intro hy
    Hint "Use `mem_leftCoset_iff` to convert coset membership into subgroup membership. Apply it to both `hx` and `hy` using `replace`:
    `replace hx := (mem_leftCoset_iff _).1 hx`
    `replace hy := (mem_leftCoset_iff _).1 hy`
    This gives g⁻¹ * x ∈ H and g⁻¹ * y ∈ H."
    replace hx :=(mem_leftCoset_iff _).1 hx
    replace hy :=(mem_leftCoset_iff _).1 hy
    Hint "We need to relate x⁻¹ * y to the elements g⁻¹ * x and g⁻¹ * y that we know are in H. Observe that x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y). Establish this with:
    `have hxy : x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group`
    The `group` tactic verifies this identity from the group axioms.
    "
    have hxy :x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group
    Hint "Rewrite the goal using `rw [{hxy}]` to express x⁻¹ * y in terms of g⁻¹ * x and g⁻¹ * y."
    rw [hxy]
    Hint "The goal is now (g⁻¹ * x)⁻¹ * (g⁻¹ * y) ∈ H. Since both g⁻¹ * x and g⁻¹ * y are in H, we can use `Subgroup.mem_of_inv_mul_mem` which says: if a ∈ H and b ∈ H then a⁻¹ * b ∈ H. Apply it with `apply Subgroup.mem_of_inv_mul_mem hx hy`."
    apply Subgroup.mem_of_inv_mul_mem hx hy
  · Hint "For the reverse direction, assume x⁻¹ * y ∈ H and show y ∈ g • H. Use `intro hxy`."
    intro hxy
    Hint "Convert `{hx} : x ∈ g • H` into `g⁻¹ * x ∈ H` using `mem_leftCoset_iff`:
    `have hgx : g⁻¹ * x ∈ H := (mem_leftCoset_iff _).1 hx`"
    have hgx : g⁻¹ * x ∈ H := (mem_leftCoset_iff _).1 hx
    Hint "To show y ∈ g • H, provide the witness (g⁻¹ * x) * (x⁻¹ * y), which is in H and satisfies g * ((g⁻¹ * x) * (x⁻¹ * y)) = y. Use `use (g⁻¹ * x) * (x⁻¹ * y)`."
    use ((g⁻¹*x) * (x⁻¹ *y))
    Hint "Use `constructor` to split the conjunction into two subgoals: membership in H, and the equation."
    constructor
    · Hint "The product of two elements in a subgroup is again in the subgroup. Use `exact Subgroup.mul_mem _ {hgx} {hxy}`."
      exact Subgroup.mul_mem _ hgx hxy
    Hint "The remaining goal is a group identity: g * ((g⁻¹ * x) * (x⁻¹ * y)) = y. Use `simp` and `group` to close it."
    simp only [smul_eq_mul, zpow_neg, zpow_one]
    group
