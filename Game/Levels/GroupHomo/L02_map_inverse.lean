import Game.Metadata
import Mathlib.Data.ZMod.Defs
-- import Mathlib

World "GroupHomomorphism"

Level 2

Title "Homomorphisms Preserve Inverses"

Introduction "
Another easy consequence of the definition of group homomorphism,  f : H →* G, is that it sends inverse to inverse, i.e ∀ h : H f (h⁻¹) = (f h)⁻¹.
"
variable {G H:Type*} [Group G] [Group H]

Statement (f : H →* G) : ∀ h : H,  f h⁻¹ = (f h)⁻¹  := by
  Hint "Observe that f(h⁻¹) * f(h) = f(h⁻¹ * h) = f(1) 1. Hence f(h) is the inverse of f(h⁻¹).

  One should begin with `intro h` to reveal the goal.
  And then establish the claim h⁻¹ * h =1
  "
  intro h
  have hh : h⁻¹ * h = 1 := by group
  Hint "Now use `f`, `map_mul` and `map_one` on {hh}. "
  apply_fun f at hh
  rw [map_mul,map_one] at hh
  Hint "It is the time to use `mul_eq_one_iff_eq_inv` to clear up {hh} and finish the proof"
  rw [mul_eq_one_iff_eq_inv] at hh
  assumption

Conclusion "You showed that f(h⁻¹) = (f h)⁻¹ for any group homomorphism. Homomorphisms respect the full group structure."

open scoped Pointwise
#check (1 : ZMod 6) +ᵥ ({1,2,3}: Set (ZMod 6))



NewTheorem mul_left_cancel map_mul mul_one map_one mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_inv
--OnlyTactic intro «have» apply_fun rw apply exact assumption
DisabledTactic group simp aesop trivial
