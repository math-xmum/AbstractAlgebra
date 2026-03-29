import Game.Metadata
-- import Mathlib

World "GroupAction"

Level 3

Introduction "
Let X be a G-set.
In this Level, we construct the natural bijection G/G_x → G x for any x∈ X.
"

open Pointwise
open scoped Pointwise
open scoped MulAction
open MulAction

variable {G X:Type*} [Group G] [MulAction G X]

#check  QuotientGroup.mk_out_eq_mul

/-- The canonical map G/G_x → orbit G x is injective. -/
private lemma orbit_map_injective (x : X) :
    Function.Injective (fun y : G ⧸ stabilizer G x => (⟨y.out • x, MulAction.mem_orbit _ _⟩ : orbit G x)) := by
  intro y1 y2
  simp
  intro H
  apply_fun (y2.out⁻¹ • ·) at H
  simp only [inv_smul_smul] at H
  rw [←mul_smul, ←MulAction.mem_stabilizer_iff] at H
  rw [←QuotientGroup.eq] at H
  simp at H
  rw [H]

/-- The canonical map G/G_x → orbit G x is surjective. -/
private lemma orbit_map_surjective (x : X) :
    Function.Surjective (fun y : G ⧸ stabilizer G x => (⟨y.out • x, MulAction.mem_orbit _ _⟩ : orbit G x)) := by
  intro ⟨y, hy⟩
  obtain ⟨g, hg⟩ := hy
  beta_reduce at hg
  simp
  use g
  have hqg : ∃ (h : stabilizer G x), (g : G ⧸ stabilizer G x).out = g * h := QuotientGroup.mk_out_eq_mul _ _
  obtain ⟨h, hh⟩ := hqg
  rw [hh, mul_smul, MulAction.mem_stabilizer_iff.1 h.2]
  exact hg

noncomputable section

Statement (x : X) : G ⧸  stabilizer G x ≃ orbit G x  := by
  Hint "We construct the equivalence by `Equiv.ofBijective`."
  apply Equiv.ofBijective
  Hint "We construct the function by sending y to y.out • x."
  show Function.Bijective (fun y : G ⧸ stabilizer G x => ⟨y.out • x, MulAction.mem_orbit _ _⟩)
  Hint "Now prove the map is bijective. First split the goal using `constructor`."
  constructor
  · Hint "The injectivity proof uses `apply_fun`, `inv_smul_smul`, `mul_smul`, `MulAction.mem_stabilizer_iff`, and `QuotientGroup.eq`."
    exact orbit_map_injective x
  · Hint "The surjectivity proof uses `QuotientGroup.mk_out_eq_mul` to relate a coset representative to the original element."
    exact orbit_map_surjective x



NewTheorem QuotientGroup.mk_out_eq_mul Equiv.ofBijective MulAction.mem_orbit MulAction.mem_stabilizer_iff SemigroupAction.mul_smul Equiv.ofBijective MulAction.stabilizer MulAction.orbit inv_smul_smul QuotientGroup.eq
NewTactic apply_fun
