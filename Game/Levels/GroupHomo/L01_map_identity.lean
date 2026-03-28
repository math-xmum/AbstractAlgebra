import Game.Metadata
-- import Mathlib

World "GroupHomomorphism"

Level 1

Introduction "
Suppose H and G are two groups.
A group (or monoid) homomorphism is a map f: H → G such that for all
h₁ h₂∈ H, f(h₁ * h₂) = f(h₁) * f(h₂).

In Mathlib, group homomorphism is represented by H →* G.
This property `∀ h₁ h₂∈ H, f(h₁ * h₂) = f(h₁) * f(h₂)` is called `map_mul`.

One basic fact is that the identity element of H is map to the
identity element of G.
This is called `map_one`

We now prove this using the cancellation law.
"
variable {G H:Type*} [Group G] [Group H]


Statement (f : H →* G) : f 1  = 1  := by
  Hint "The idea is to use 1 * 1 = 1. (This can be done by invoking `mul_one (1:H)`).
  Here we should use `(1:H)` to indicate that `1` is the identity element in H.
  Use `have` to establish this claim."
  have h1 : (1:H) * 1 = 1 := mul_one (1:H)
  Hint "Now let us apply f on the both sides of {h1}. This can be done by `apply_fun f at {h1}` "
  apply_fun f at h1
  Hint "Let us use `map_mul` on {h1} to obtain f 1 * f 1  = f 1"
  rw [map_mul] at h1
  Hint "Apply `mul_one` again to obtain f 1 * f 1= f 1 * 1. Here one must use `nth_rw` to control the rewriting place."
  nth_rw 3 [<-mul_one (f 1)] at h1
  Hint "Finally one can apply `mul_left_cancel` to obtain the goal."
  exact mul_left_cancel h1

NewTheorem mul_left_cancel map_mul mul_one GroupHom.intro mul_eq_left Function.leftInverse_iff_comp Function.rightInverse_iff_comp MulEquiv.intro
NewTactic apply_fun beta_reduce
