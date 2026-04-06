import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "GroupAction"

Level 2

Introduction "
The **stabilizer** of `x : X` under a `G`-action is `G_x = {g : G | g • x = x}`.
In Lean, this is `MulAction.stabilizer G x`, and `MulAction.mem_stabilizer_iff`
converts `g ∈ stabilizer G x ↔ g • x = x`.

If `y = g • x` (same orbit), then the stabilizers are conjugate: `G_y = g G_x g⁻¹`.

In Lean, conjugation `h ↦ g * h * g⁻¹` is `MulAut.conj g`, and its action on
subgroups is written `(MulAut.conj g) • H`. We also use `simp_rw` -- a variant
of `rw` that rewrites inside binders and quantifiers.
"

open Pointwise
open scoped Pointwise
open scoped MulAction
open MulAction

variable {G X:Type*} [Group G] [MulAction G X]

#check  QuotientGroup.mk_out_eq_mul


Statement (x y : X) (g:G) (hxy : y = g • x): (MulAut.conj g) • stabilizer G x = stabilizer G y  := by
  Hint "To show two subgroups are equal, prove they have the same elements. Use `ext h`
  to reduce to `h ∈ LHS ↔ h ∈ RHS`."
  ext h
  Hint "Use `rw [Subgroup.mem_smul_pointwise_iff_exists]` to express membership in a
  conjugate subgroup as an existential: `∃ k, k ∈ stabilizer G x ∧ g * k * g⁻¹ = h`."
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  Hint "Now unfold the stabilizer condition `k ∈ stabilizer G x` to `k • x = x`.
  Since the term is inside a binder (under `∃`), plain `rw` fails.
  Use `simp_rw [MulAction.mem_stabilizer_iff]` instead -- `simp_rw` rewrites
  under binders."
  simp_rw [MulAction.mem_stabilizer_iff]
  Hint "Expand `MulAut.conj g` using `MulAut.smul_def` and `MulAut.conj_apply`:
  `simp_rw [MulAut.smul_def, MulAut.conj_apply]`"
  simp_rw [MulAut.smul_def, MulAut.conj_apply]
  Hint "Use `constructor` to split the `↔`."
  constructor
  · Hint "Use `intro H` then `obtain ⟨k, Hk1, Hk2⟩ := H` to get `k` with
    `k • x = x` and `g * k * g⁻¹ = h`."
    intro H
    obtain ⟨k,Hk1,Hk2⟩ := H
    Hint "Rewrite the goal using `{hxy}` (to replace `y`), then `{Hk2}` (to replace `h`),
    and `{Hk1}` (the stabilizer condition). Use `nth_rw` when needed to control which
    occurrence gets rewritten."
    rw [hxy]
    rw [<-Hk2]
    nth_rw 2 [<-Hk1]
    Hint "Convert `(g * k * g⁻¹ * g) • x` using `mul_smul` (which says `(a*b) • x = a • (b • x)`).
    Use `repeat rw [<-mul_smul]` to expand, then `group` to simplify."
    repeat rw [<-mul_smul]
    Hint "The goal is now pure group arithmetic on the elements. Use `group` to close it."
    group
  · Hint "Use `intro H` to assume `h • y = y`."
    intro H
    Hint "We need `k` with `k • x = x` and `g * k * g⁻¹ = h`. Since `h = g * k * g⁻¹`
    iff `k = g⁻¹ * h * g`, provide the witness: `use g⁻¹ * h * g`"
    use g⁻¹ * h * g
    Hint "Use `constructor` to split."
    constructor
    · Hint "Show `(g⁻¹ * h * g) • x = x`. First flip `{hxy}` with `replace hxy := hxy.symm`
      to get `g • x = y`, then use `smul_eq_iff_eq_inv_smul` to rewrite it as `x = g⁻¹ • y`."
      replace hxy := hxy.symm
      rw [smul_eq_iff_eq_inv_smul] at hxy
      Hint "Rewrite with `{hxy}` and `{H}`, expand `mul_smul`, then close with `group`."
      rw [hxy]
      nth_rw 2 [<-H]
      repeat rw [<-mul_smul]
      group
    · Hint "The equation `g * (g⁻¹ * h * g) * g⁻¹ = h` is pure group arithmetic. Use `group`."
      group

NewTheorem MulAction.mem_orbit MulAction.mem_stabilizer_iff SemigroupAction.mul_smul Equiv.ofBijective MulAction.stabilizer MulAction.orbit inv_smul_smul QuotientGroup.eq smul_eq_iff_eq_inv_smul Subgroup.mem_smul_pointwise_iff_exists MulAut.conj_apply MulAut.smul_def
-- NewTactic moved to BasicLean
