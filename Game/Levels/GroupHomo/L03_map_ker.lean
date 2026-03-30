import Game.Metadata
-- import Mathlib

World "GroupHomomorphism"

Level 3

Title "Kernel Is Closed Under Conjugation"

Introduction "
Let  f : G →* H be a group homomorphism.
Then the kernel of f is defined by

Ker(f) := {g ∈ G | f(g) = 1}

It is easy to see that Ker(f) is a subgroup of G.
But Ker(f) satisfies one additional property:

∀ g ∈ G, x ∈ Ker(f),  g x g⁻¹ ∈ f
We now prove this property.

A subgroup satisfies the above property is called a normal subgroup of G.

Note that, if G is Abelian, then g x g⁻¹ = x ∈ Ker(f) for all x ∈ Ker(f), i.e. all subgroups of G are normal.
But this is not the case for general groups.

"
variable {G H:Type*} [Group G] [Group H]

Statement (f : G →* H) :
∀ g x : G,  x ∈ f.ker → g * x * g⁻¹ ∈ f.ker  := by
  Hint "Use intro"
  intro g x hx
  Hint "Use MonoidHom.mem_ker on the goal and {hx}"
  rw [MonoidHom.mem_ker]
  rw [MonoidHom.mem_ker] at hx
  Hint "Use `f` and `map_mul` and `map inv` on the goal"
  rw [map_mul,map_inv]
  rw [map_mul]
  Hint "Use the assumption {hx}."
  rw [hx]
  Hint "Use `group` to finish the goal"
  group

Conclusion "You proved that the kernel of a homomorphism is closed under conjugation, which means it is a normal subgroup."

open scoped Pointwise

NewTheorem MonoidHom.mem_ker map_inv
DisabledTactic group simp aesop trivial
--OnlyTactic intro «have» apply_fun rw apply exact assumption
