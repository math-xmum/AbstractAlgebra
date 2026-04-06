import Game.Metadata
-- import Mathlib

World "GroupHomomorphism"

Level 3

Introduction "
The **kernel** of a group homomorphism `f : G →* H` is

`ker(f) := {g : G | f(g) = 1}`

In Lean, `f.ker` is the kernel and `MonoidHom.mem_ker` converts between
`x ∈ f.ker` and `f x = 1`.

We prove that the kernel is closed under conjugation:
for all `g x : G`, if `x ∈ ker(f)` then `g * x * g⁻¹ ∈ ker(f)`.

A subgroup with this property is called a **normal subgroup**.
(In an abelian group every subgroup is normal, but not in general.)
"
variable {G H:Type*} [Group G] [Group H]

Statement (f : G →* H) :
∀ g x : G,  x ∈ f.ker → g * x * g⁻¹ ∈ f.ker  := by
  Hint "The goal starts with `∀ g x`. Use `intro g x hx` to introduce the variables
  and the hypothesis `hx : x ∈ f.ker`."
  intro g x hx
  Hint "Both the goal and `{hx}` involve `∈ f.ker`. Use `MonoidHom.mem_ker` to unfold
  these into equations `f _ = 1`:
  `rw [MonoidHom.mem_ker]` on the goal, and `rw [MonoidHom.mem_ker] at {hx}`."
  rw [MonoidHom.mem_ker]
  rw [MonoidHom.mem_ker] at hx
  Hint "The goal is `f (g * x * g⁻¹) = 1`. Expand using `map_mul` and `map_inv`:
  `rw [map_mul, map_inv]` then `rw [map_mul]`"
  rw [map_mul,map_inv]
  rw [map_mul]
  Hint "Now substitute `{hx} : f x = 1` into the goal with `rw [{hx}]`."
  rw [hx]
  Hint "The goal reduces to `f g * 1 * (f g)⁻¹ = 1`, which is pure group arithmetic.
  Use `group` to close it."
  group



open scoped Pointwise

NewTheorem MonoidHom.mem_ker map_inv
DisabledTactic group simp aesop trivial
--OnlyTactic intro «have» apply_fun rw apply exact assumption
