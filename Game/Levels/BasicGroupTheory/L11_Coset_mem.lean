import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 11

Introduction "
Let H be a subset of a group G. For any element g in G, the **left coset** of H by g is the set
g • H := {g * h | h ∈ H}.

In this level we prove a useful characterization:
x ∈ g • H  if and only if  g⁻¹ * x ∈ H.

Intuitively, x belongs to g • H precisely when \"undoing\" g from x lands back in H. This fact is called `mem_leftCoset_iff` in Mathlib.
"

open Monoid Group
open scoped Pointwise
open Pointwise



variable {G : Type*} [Group G] {g x:G} {H : Set G}

--instance : HSMul G (Set G) (Set G):=inferInstance

Statement : x ∈ g • H ↔ g⁻¹ * x ∈ H := by
  constructor
  · intro h1
    Hint "Unfolding the definition, `h1 : x ∈ g • H` means there exists some element h in G with h ∈ H and g * h = x. The `obtain` tactic lets you decompose this existential:
    `obtain ⟨h, hh1, hh2⟩ := h1`
    This gives you `h : G`, `hh1 : h ∈ H`, and `hh2 : g * h = x`.
    "
    obtain ⟨h, hh1,hh2⟩ := h1
    Hint "The hypothesis `{hh2}` may have unnecessary coercions. Use `simp only [Set.mem_image, smul_eq_mul] at {hh2}` to simplify it into a clean equation."
    simp only [Set.mem_image, smul_eq_mul] at hh2
    Hint "Now rewrite the goal using `rw [<-{hh2}]` to replace x with g * h."
    rw [<-hh2]
    Hint "After rewriting, `rw [inv_mul_cancel_left]` simplifies g⁻¹ * (g * h) to h. Then `assumption` closes the goal since h ∈ H is exactly what we need."
    rw [inv_mul_cancel_left]
    assumption
  · Hint "For the reverse direction, use `intro h1` to assume g⁻¹ * x ∈ H."
    intro h1
    Hint "We need to exhibit an element of H whose left-multiply by g gives x. The witness is g⁻¹ * x. Use `use g⁻¹ * x`."
    use g⁻¹*x
    Hint "Now `simp only [mul_inv_cancel_left]` simplifies g * (g⁻¹ * x) to x, and `assumption` finishes the proof since g⁻¹ * x ∈ H."
    refine ⟨h1, ?_⟩
    simp only [smul_eq_mul, mul_inv_cancel_left]
