import Game.Metadata
import Game.Generator.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
-- import Mathlib

World "GroupAction"

Level 2

Introduction "
Let X be a G-set.
Let G_x := { g ∈ G | g • x = x} be the stabilizer for a point x ∈ G.

Suppose x y ∈ X are in the same orbit, i.e. exists g ∈ G such that y = g • x.
Then we have G_y = g G_x g⁻¹.

Conjugation action h ↦ g h g⁻¹ is denote by MulAut.conj g • h. This action induces an action on the set of subgroups of G.
Now g H g⁻¹ is denoted by (MulAut.conj g) • H in Mathlib.

We are going to prove this.

"

open Pointwise
open scoped Pointwise
open scoped MulAction
open MulAction

variable {G X:Type*} [Group G] [MulAction G X]

#check  QuotientGroup.mk_out_eq_mul

/-- Forward direction: if k stabilizes x and h = g * k * g⁻¹, then h stabilizes y = g • x. -/
private lemma conj_stab_fwd {x y : X} {g h : G} (hxy : y = g • x)
    (H : ∃ k, k • x = x ∧ g * k * g⁻¹ = h) : h • y = y := by
  obtain ⟨k, Hk1, Hk2⟩ := H
  subst hxy; subst Hk2
  show (g * k * g⁻¹) • (g • x) = g • x
  rw [mul_smul, mul_smul, inv_smul_smul, Hk1]

/-- Backward direction: if h stabilizes y = g • x, then g⁻¹ * h * g stabilizes x. -/
private lemma conj_stab_bwd {x y : X} {g h : G} (hxy : y = g • x)
    (H : h • y = y) : (g⁻¹ * h * g) • x = x ∧ g * (g⁻¹ * h * g) * g⁻¹ = h := by
  constructor
  · replace hxy := hxy.symm
    rw [smul_eq_iff_eq_inv_smul] at hxy
    rw [hxy]; nth_rw 2 [←H]
    repeat rw [←mul_smul]; group
  · group

Statement (x y : X) (g:G) (hxy : y = g • x): (MulAut.conj g) • stabilizer G x = stabilizer G y  := by
  Hint "To show two sets A and B are equal, it suffices to show that x ∈ A ↔ x ∈ B. This can be done by  `ext`. Try `ext h`. "
  ext h
  Hint "Rewrite using the lemma `Subgroup.mem_smul_pointwise_iff_exists` to transform the membership condition in the set into an existential statement. "
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  Hint "Use `MulAction.mem_stabilizer_iff` to rewrite the goal.
  Since you are rewriting an inner term `rw` will fail. Try `simp_rw [MulAction.mem_stabilizer_iff]` instead."
  simp_rw [MulAction.mem_stabilizer_iff]
  Hint "Now use `MulAut.smul_def` and `MulAut.conj_apply` to rewrite `MulAut.conj_apply`. BTW: Use `simp` also works."
  simp_rw [MulAut.smul_def, MulAut.conj_apply]
  Hint "Use `constructor` to split the goal. "
  constructor
  · Hint "Introduce the hypothesis use `intro`."
    intro H
    exact conj_stab_fwd hxy H
  · Hint "Introduce the hypothesis. "
    intro H
    Hint "The condition g * s * g⁻¹ = h equivalent to s = g⁻¹ * h * g. Try `use g⁻¹ * h * g`."
    use g⁻¹ * h * g
    exact conj_stab_bwd hxy H

NewTheorem MulAction.mem_orbit MulAction.mem_stabilizer_iff SemigroupAction.mul_smul Equiv.ofBijective MulAction.stabilizer MulAction.orbit inv_smul_smul QuotientGroup.eq smul_eq_iff_eq_inv_smul Subgroup.mem_smul_pointwise_iff_exists MulAut.conj_apply MulAut.smul_def
NewTactic apply_fun simp_rw
