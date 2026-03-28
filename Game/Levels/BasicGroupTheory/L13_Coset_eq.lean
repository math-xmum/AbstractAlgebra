import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 13

Introduction "
Let H be a subgroup of G.
Then g • H = k • H if and only if k⁻¹ * g ∈ H.

We now prove only if part of this statement first.
"

open Monoid Group
open scoped Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}
open Pointwise

Statement (k : G) :(g • (H : Set G)  = k • (H : Set G)) → k⁻¹ * g ∈ H:= by
    intro h1
    Hint "Note that g ∈ g • H. "
    have hg : g ∈ g • (H :Set G) := by
      Hint "Use 1"
      use 1
      Hint "By definition 1 is certainly in H, but you still need to explicitly point it out using `Subgroup.one_mem' "
      simp [Subgroup.one_mem]
    Hint "Now use {h1} by rewrite the right hand side of {hg} (rw [{h1}] at {hg}) "
    rw [h1] at hg
    Hint "Apply `mem_leftCoset_iff' and the rest is trivial. "
    apply (mem_leftCoset_iff k).1
    assumption


NewTheorem Subgroup.one_mem mem_leftCoset_iff
