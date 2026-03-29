import Game.Metadata
-- import Mathlib

World "CosetsAndLagrange"

Level 1

Introduction "
Let H be a subgroup of G.
The subset g • H := {gh | h∈H} for some g∈G is called a left coset of H.

We first prove the simple fact that
x ∈ g • H ↔ g⁻¹ * x ∈ H

The above lemma is called `mem_leftCoset_iff' in Mathlib.
"

open Monoid Group
open scoped Pointwise
open Pointwise



variable {G : Type*} [Group G] {g x:G} {H : Set G}

--instance : HSMul G (Set G) (Set G):=inferInstance

private lemma coset_mem_forward (h1 : x ∈ g • H) : g⁻¹ * x ∈ H := by
  obtain ⟨h, hh1, hh2⟩ := h1
  simp at hh2; rw [← hh2]; simp; exact hh1

Statement : x ∈ g • H ↔ g⁻¹ * x ∈ H := by
  constructor
  · Hint "Note that x ∈ g • H means ∃ h: G,  h ∈ H ∧  g * h = x. Use `obtain' to obtain the anxiety element h.
    For example, one can use
    `obtain ⟨h, hh1,hh2⟩ := h1'
    "
    Hint "The goal can be cleared by `simp'/`group' and `assumption'"
    intro h1
    exact coset_mem_forward h1
  · Hint "Intro the assumption."
    intro h1
    Hint " Use `g⁻¹ * x'"
    use g⁻¹*x
    Hint "The goal can be cleared by `simp'/`group' and `assumption'"
    exact ⟨h1, by simp⟩
