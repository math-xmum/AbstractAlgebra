import Game.Metadata
import Mathlib.GroupTheory.Coset.Basic

World "GroupAction"

Level 4

Title "Group Acts Transitively on Cosets"

Introduction "
The group G acts on the set of left cosets G/H by left multiplication:
g sends the coset kH to the coset (gk)H.

This action is transitive, meaning any coset can be reached from any other.
In fact, every coset q ∈ G/H has a representative g ∈ G such that gH = q.

In Lean, the quotient `G ⧸ H` is the set of left cosets of a subgroup H.
The map `QuotientGroup.mk : G → G ⧸ H` sends each element to its coset.
This map is surjective: every coset has a preimage.

Use `QuotientGroup.mk_surjective` to finish the proof.
"

open QuotientGroup

variable {G : Type*} [Group G] (H : Subgroup G)

Statement : ∀ q : G ⧸ H, ∃ g : G, (g : G ⧸ H) = q := by
  Hint "We need to show every coset has a representative. Use `intro q` to fix a coset."
  intro q
  Hint "Now use `exact QuotientGroup.mk_surjective q` to apply the surjectivity of the quotient map."
  exact QuotientGroup.mk_surjective q

Conclusion "
Every coset in G/H has a representative in G. This is the key fact that makes
the left multiplication action on cosets transitive: to send the coset H = 1·H
to any coset gH, just act by g.
"

NewTheorem QuotientGroup.mk_surjective
