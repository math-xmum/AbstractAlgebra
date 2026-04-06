import Game.Metadata
-- import Mathlib

World "GroupHomomorphism"

Level 2

Introduction "
A group homomorphism `f : H →* G` preserves inverses: for all `h : H`,
`f(h⁻¹) = (f h)⁻¹`.

**Key idea:** Show that `f(h⁻¹) * f(h) = 1`, which forces `f(h⁻¹)` to be the
inverse of `f(h)`. We use `h⁻¹ * h = 1`, apply `f`, then invoke `map_mul` and `map_one`.
"
variable {G H:Type*} [Group G] [Group H]

Statement (f : H →* G) : ∀ h : H,  f h⁻¹ = (f h)⁻¹  := by
  Hint "The goal has a `∀ h`. Use `intro h` to fix an arbitrary element `h : H`.
  Then establish `h⁻¹ * h = 1` using `have`. The `group` tactic can close this
  arithmetic sub-goal automatically."
  intro h
  have hh : h⁻¹ * h = 1 := by group
  Hint "Apply `f` to both sides with `apply_fun f at {hh}`, then rewrite the left side
  using `map_mul` and the right side using `map_one`:
  `rw [map_mul, map_one] at {hh}`"
  apply_fun f at hh
  rw [map_mul,map_one] at hh
  Hint "Now `{hh}` says `f h⁻¹ * f h = 1`. The theorem `mul_eq_one_iff_eq_inv` converts
  `a * b = 1 ↔ a = b⁻¹`. Rewrite `{hh}` with it:
  `rw [mul_eq_one_iff_eq_inv] at {hh}`
  Then `assumption` closes the goal."
  rw [mul_eq_one_iff_eq_inv] at hh
  assumption

open scoped Pointwise
#check (1 : ZMod 6) +ᵥ ({1,2,3}: Set (ZMod 6))



NewTheorem mul_left_cancel map_mul mul_one map_one mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_inv
--OnlyTactic intro «have» apply_fun rw apply exact assumption
DisabledTactic group simp aesop trivial
