import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 13

Introduction "
When do two left cosets coincide? The answer is:
g • H = k • H  if and only if  k⁻¹ * g ∈ H.

In this level we prove the forward direction: if the cosets are equal, then k⁻¹ * g ∈ H.

The key idea is that g always belongs to its own coset g • H (since g = g * 1 and 1 ∈ H). If g • H = k • H, then g ∈ k • H, and the result follows from the characterization proved in Level 11.
"

open Monoid Group
open scoped Pointwise

variable {G : Type*} [Group G] {g k :G} {H : Subgroup G}
open Pointwise

Statement  :(g • (H : Set G)  = k • (H : Set G)) → k⁻¹ * g ∈ H:= by
    intro h1
    Hint "Our first step is to show that g ∈ g • H. We introduce this as an intermediate claim using `have`."
    have hg : g ∈ g • (H :Set G) := by
      Hint "To show g ∈ g • H, we need an element h ∈ H with g * h = g. The witness is 1 (the identity). Use `use 1`."
      use 1
      Hint "We must show 1 ∈ H and g * 1 = g. The theorem `Subgroup.one_mem` proves that 1 belongs to any subgroup. Use `simp [Subgroup.one_mem]` to close both subgoals."
      exact ⟨Subgroup.one_mem _, by simp only [smul_eq_mul, mul_one]⟩
    Hint "Since g • H = k • H (by `{h1}`), we can replace g • H with k • H in `{hg}`. Use `rw [{h1}] at {hg}` to obtain g ∈ k • H."
    rw [h1] at hg
    Hint "Now g ∈ k • H. By `mem_leftCoset_iff`, this is equivalent to k⁻¹ * g ∈ H. Apply it with `apply (mem_leftCoset_iff k).1` and then `assumption` finishes the proof."
    apply (mem_leftCoset_iff k).1
    assumption


NewTheorem Subgroup.one_mem mem_leftCoset_iff
