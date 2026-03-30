import Game.Metadata

World "GroupBasics"

Level 6

Title "Subgroup Criterion"

Introduction "
A subgroup of a group $G$ is a nonempty subset $H$ of $G$ that is closed under
multiplication and inverses.

There is a useful criterion: if $H$ is nonempty and for all $a, b ∈ H$ we have
$a * b⁻¹ ∈ H$, then $H$ is a subgroup of $G$.

Why does this work?
- Since $H$ is nonempty, pick $x ∈ H$. Then $x * x⁻¹ = 1 ∈ H$.
- For any $a ∈ H$, we get $1 * a⁻¹ = a⁻¹ ∈ H$ (inverse closure).
- For any $a, b ∈ H$, we get $b⁻¹ ∈ H$, so $a * (b⁻¹)⁻¹ = a * b ∈ H$ (multiplication closure).

Mathlib provides `Subgroup.ofDiv` which constructs a `Subgroup G` from exactly
these hypotheses. Use it to solve this level.
"
open Monoid Group

variable {G : Type*} [Group G] {H : Set G}

set_option linter.unusedTactic false in
Statement (h1 : H.Nonempty) (h2 : ∀ᵉ (x ∈ H) (y ∈ H), x * y⁻¹ ∈ H) :
    Subgroup G := by
  Hint "The hypotheses `h1` and `h2` are exactly what `Subgroup.ofDiv` needs.
  Use `exact Subgroup.ofDiv H h1 h2` to construct the subgroup."
  exact Subgroup.ofDiv H h1 h2

Conclusion "A nonempty subset closed under x * y⁻¹ is a subgroup. Mathlib's `Subgroup.ofDiv` packages this criterion."

NewTheorem Subgroup.ofDiv Subgroup.mem_of_inv_mul_mem Subgroup.mem_of_mem_mul_inv Subgroup.inv_mem Subgroup.mul_mem
