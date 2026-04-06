import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 12

Introduction "
All left cosets of H have the same size. More precisely, for any g, k in G there is a natural bijection between g • H and k • H, given by x ↦ (k * g⁻¹) * x.

In Lean 4, a bijection between two types is represented by `Equiv α β`. An `Equiv` bundles four pieces of data: a forward map `toFun`, an inverse map `invFun`, and proofs that they are mutual inverses (`left_inv` and `right_inv`).

In this level you will construct such an `Equiv` explicitly.
"

open Monoid Group

variable {G : Type*} [Group G] {g k:G} {H : Set G}


open scoped Pointwise
open Pointwise

--instance : HSMul G (Set G) (Set G):=inferInstance

Statement :
  Equiv (g • H :Set G) (k • H : Set G):= by
  Hint "We build the `Equiv` by supplying its four fields. The `refine` tactic lets us provide a structure with holes (`?fieldName`) to fill in later."
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  Hint "We now define the forward map from g • H to k • H."
  case toFun =>
    Hint "Define the map by x ↦ (k * g⁻¹) * x. Since x is an element of the subtype g • H, the output must be a subtype element of k • H, so we need to prove that (k * g⁻¹) * x ∈ k • H.
    "
    exact fun x => ⟨(k * g⁻¹)*x, by
      Hint "Since x ∈ g • H, there exists h ∈ H such that g * h = x. Use `obtain` to decompose `x.2`."
      obtain ⟨h,b,hh⟩ := x.2
      Hint "Simplify the coercion in `{hh}` using `simp at {hh}`."
      simp at hh
      Hint "Now rewrite using `{hh}` so that x becomes g * h, then `group` simplifies k * g⁻¹ * (g * h) to k * h."
      rw [<-hh]
      group
      Hint "Now `use h` to provide the witness, and `trivial` finishes the proof."
      use h
      trivial⟩
  Hint "Now construct the inverse map from k • H to g • H. The argument is symmetric: use x ↦ (g * k⁻¹) * x."
  case invFun =>
    Hint "This case is analogous to the forward map, with g and k swapped."
    exact fun x => ⟨(g * k⁻¹)*x, by
      obtain ⟨h,b,hh⟩ := x.2
      simp at hh
      rw [<-hh]
      group
      Hint "Use `use h` and `trivial` to finish, just like the forward case."
      use h
      trivial⟩
  case left_inv =>
    Hint "`left_inv` asks us to show that applying invFun after toFun returns the original element. This means for all x, we need invFun (toFun x) = x. Use `intro x` to fix an element."
    intro x
    Hint "Since elements of g • H are subtypes, equality reduces to equality of the underlying group elements. The `ext` tactic does exactly this reduction."
    ext
    Hint "Use `simp` to simplify coercions in the goal."
    simp
    Hint "The `group` tactic closes goals that follow from the group axioms. Here it proves g * k⁻¹ * (k * g⁻¹ * x) = x."
    group
  case right_inv =>
    Hint "This is symmetric to `left_inv`. Use `intro x`, then `ext`, and finish with `group`."
    intro x
    ext;group


NewTheorem Set
