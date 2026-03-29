import Game.Metadata
import Mathlib.GroupTheory.Subgroup.Center

World "GroupAction"

Level 5

Title "Center and Conjugacy Classes"

Introduction "
The center Z(G) of a group G consists of elements that commute with every element of G.
Equivalently, g ∈ Z(G) if and only if the conjugacy class of g is the singleton {g}.

In Lean, the center of a group is `Subgroup.center G`, and the characterization is
given by `Subgroup.mem_center_iff`: an element z is in the center if and only if
g * z = z * g for all g.

The center is always a normal subgroup of G. For abelian groups, Z(G) = G.
"

variable {G : Type*} [Group G]

Statement (g : G) : g ∈ Subgroup.center G ↔ ∀ h : G, h * g = g * h := by
  Hint "This is exactly the characterization given by `Subgroup.mem_center_iff`."
  exact Subgroup.mem_center_iff

Conclusion "
The center Z(G) = \\{g ∈ G | gh = hg for all h ∈ G\\} captures the 'abelian part' of a group.
When G acts on itself by conjugation, the center is precisely the set of fixed points:
g ∈ Z(G) iff the conjugacy class of g is \\{g\\}.

This viewpoint connects the center to the class equation:
|G| = |Z(G)| + Σ [G : C_G(gᵢ)], summing over representatives of non-trivial conjugacy classes.
"

NewTheorem Subgroup.mem_center_iff Subgroup.center
