import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "GroupAction"

Level 1

Introduction "
Welcome to the Group Action world!

Let `G` act on a set `X`. For `x : X`, the **orbit** of `x` is
`Gx = {g • x | g : G}`. In Lean, `MulAction.orbit G x` is this set,
and `z ∈ orbit G x` means `∃ g : G, g • x = z`.

We prove: `orbit G x = orbit G y ↔ ∃ g : G, g • x = y`.

Two orbits are equal precisely when one element can be moved to the other.
"

open Pointwise
open scoped Pointwise
open scoped MulAction
open MulAction

variable {G X:Type*} [Group G] [MulAction G X]

#check  QuotientGroup.mk_out_eq_mul


Statement (x y : X) :  MulAction.orbit G x = MulAction.orbit G y ↔ ∃ g:G , g • x = y := by
  Hint "The goal is an `↔`. Use `constructor` to split into the two directions."
  constructor
  · Hint "Use `intro H` to assume the orbits are equal."
    intro H
    Hint "Since `y ∈ orbit G y` (via `1 • y = y`), and orbits are equal, `y ∈ orbit G x`.
    Establish this: `have h1 : y ∈ orbit G y` then prove it with `use 1` and
    `apply MulAction.one_smul`."
    have h1: y ∈ orbit G y := by
      use 1
      apply MulAction.one_smul
    Hint "Rewrite `{h1}` using `{H}`: `rw [<-{H}] at {h1}`. Now `{h1} : y ∈ orbit G x`,
    which is exactly `∃ g, g • x = y`."
    rw [<-H] at h1
    Hint "The goal is now exactly `{h1}`. Use `exact {h1}`."
    exact h1
  · Hint "Use `intro H` to assume `∃ g, g • x = y`."
    intro H
    Hint "Unpack with `obtain ⟨g, hg⟩ := H` to get `g : G` and `hg : g • x = y`."
    obtain ⟨g,hg⟩ := H
    Hint "To show two sets are equal, use `ext z` to prove `z ∈ orbit G x ↔ z ∈ orbit G y`."
    ext z
    Hint "Use `constructor` to split the `↔`."
    constructor
    · Hint "Assume `z ∈ orbit G x`, i.e., `∃ k, k • x = z`. If `k • x = z` and `g • x = y`,
      then `(k * g⁻¹) • y = k • x = z`. Use `obtain`, `use k * g⁻¹`, then rewrite with
      `mul_smul` and `{hg}`. Apply `beta_reduce at *` if needed to simplify."
      intro hz
      obtain ⟨k,Hk⟩:= hz
      use k * g⁻¹
      beta_reduce at *
      rw [<-hg]
      rw [<-mul_smul]
      rw [<-Hk]
      group
    · Hint "The reverse direction is similar: if `k • y = z`, use `k * g` to witness
      `z ∈ orbit G x`."
      intro hz
      obtain ⟨k,Hk⟩:= hz
      use k * g
      beta_reduce at *
      rw [<-Hk]
      rw [<-hg]
      rw [<-mul_smul]

NewTheorem SemigroupAction.mul_smul MulAction.one_smul Set.range MulAction.orbit
OnlyTactic intro constructor group rw beta_reduce nth_rw obtain ext
