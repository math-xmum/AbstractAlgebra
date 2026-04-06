import Game.Metadata
-- import Mathlib

World "GroupHomomorphism"

Level 1

Introduction "
Welcome to the Group Homomorphism world!

A **group homomorphism** is a map `f : H → G` between two groups satisfying
`f(h₁ * h₂) = f(h₁) * f(h₂)` for all `h₁ h₂ : H`.

In Lean/Mathlib, the type of group homomorphisms is written `H →* G`,
and the multiplicativity property is the theorem `map_mul`.

Our first result: a homomorphism sends the identity to the identity,
i.e., `f 1 = 1`. We will prove this from scratch using the cancellation law.

**Key idea:** start from `1 * 1 = 1` in `H`, apply `f` to both sides,
then cancel.
"
variable {G H:Type*} [Group G] [Group H]


Statement (f : H →* G) : f 1  = 1  := by
  Hint "We start from the fact `1 * 1 = 1` in `H`. The theorem `mul_one (1:H)` proves this.
  We write `(1:H)` to tell Lean that `1` lives in the group `H`.

  Use the `have` tactic to introduce this as a local hypothesis:
  `have h1 : (1:H) * 1 = 1 := mul_one (1:H)`"
  have h1 : (1:H) * 1 = 1 := mul_one (1:H)
  Hint "Now apply `f` to both sides of `{h1}`. The tactic `apply_fun` does exactly this:
  `apply_fun f at {h1}`

  The `apply_fun` tactic applies a function to both sides of an equation in a hypothesis."
  apply_fun f at h1
  Hint "Now `{h1}` says `f (1 * 1) = f 1`. Rewrite the left side using `map_mul` to get `f 1 * f 1 = f 1`:
  `rw [map_mul] at {h1}`"
  rw [map_mul] at h1
  Hint "We want to cancel `f 1` from both sides. To set up for `mul_left_cancel`,
  rewrite the right side as `f 1 * 1` using `mul_one`.

  We need `nth_rw` here (not `rw`) to control *which* occurrence gets rewritten.
  `nth_rw 3` targets the 3rd occurrence of `f 1`:
  `nth_rw 3 [<-mul_one (f 1)] at {h1}`"
  nth_rw 3 [<-mul_one (f 1)] at h1
  Hint "Now `{h1}` says `f 1 * f 1 = f 1 * 1`. The theorem `mul_left_cancel` cancels
  a common left factor from both sides of an equation. Use:
  `exact mul_left_cancel {h1}`"
  exact mul_left_cancel h1

NewTheorem mul_left_cancel map_mul mul_one GroupHom.intro mul_eq_left Function.leftInverse_iff_comp Function.rightInverse_iff_comp MulEquiv.intro
-- NewTactic moved to BasicLean
