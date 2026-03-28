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


Statement (x : X) : G ⧸  stabilizer G x ≃ orbit G x  := by
  Hint "We construct the equivalence by `Equiv.ofBijective`."
  apply Equiv.ofBijective
  Hint "Pick the 2nd goal to construct the map use `pick_goal 2`."
  pick_goal 2
  · Hint "Introduce the variable"
    intro y
    Hint "Use {y}.out to act on {x}. "
    use y.out • x
    Hint "Show that {y}.out • x is in the orbit by `MulAction.mem_orbit`."
    apply MulAction.mem_orbit
  Hint "Now prove the map is bijective. First split the goal using `constructor`."
  constructor
  · Hint "Introduce the variable"
    intro y1 y2
    Hint "Simplify the goal into human readable form by `simp`."
    simp
    Hint "Introduce the assumption."
    intro H
    Hint "Multiply y2.out⁻¹ on the both sides of {H}. Try `apply_fun (y2.out⁻¹ • ·) at {H}`.
    "
    apply_fun (y2.out⁻¹ • ·) at H
    Hint "Note that a⁻¹ • a • x = x. Use `simp` to simplify the goal. "
    simp only [inv_smul_smul] at H
    Hint "Now one use `MulAction.mem_stabilizer_iff` to show that y2.out⁻¹ y1.out ∈ stablizer G x."
    Hint "One may need `mul_smul` to rewrite {H} first."
    rw [<-mul_smul,<-MulAction.mem_stabilizer_iff] at H
    Hint "Now we conclude that [{y2}.out] = [{y1}.out] using `QuotientGroup.eq`. "
    rw [<-QuotientGroup.eq] at  H
    Hint "Simplify {H}"
    simp at H
    Hint "Now it is clear."
    rw [H]
  · Hint "Introduce the variables by `intro ⟨y, hy⟩`. "
    intro ⟨y,hy⟩
    Hint "y ∈ orbit G x means that there is g such that  g • x = y. Use `obtain` to get g and the claim. "
    obtain ⟨g,hg⟩ := hy
    Hint "Do beta_reduction by `beta_reduce at {hg}` or `simp at {hg}`."
    beta_reduce at hg
    Hint "Simplify the goal into human readable form by `simp`."
    simp
    Hint "Use the image of {g} in the coset space. Because of automatically coercion, one can write `use g`. "
    use g
    Hint "Note that [{g}].out = {g}* h for some h ∈ stabilizer G x. Use tactic `have` and theorem `QuotientGroup.mk_out_eq_mul` to obtain the claim."
    have hqg : ∃ (h : stabilizer G x), (g: G ⧸  stabilizer G x).out = g * h := QuotientGroup.mk_out_eq_mul _ _
    Hint "Now obtain h and the assumption of h"
    obtain ⟨h, hh⟩ := hqg
    Hint "The rest is clear by {hh} and {h} • x = x. One should use `mul_smul` and `MulAction.mem_stabilizer_iff`. "
    rw [hh,mul_smul]
    rw [MulAction.mem_stabilizer_iff.1 h.2]
    exact hg



NewTheorem QuotientGroup.mk_out_eq_mul Equiv.ofBijective MulAction.mem_orbit MulAction.mem_stabilizer_iff mul_smul Equiv.ofBijective MulAction.stabilizer MulAction.orbit inv_smul_smul QuotientGroup.eq
NewTactic apply_fun
