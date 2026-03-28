import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "GroupAction"

Level 1

Introduction "
Let X be a G-set.
For x ∈ X, let Gx be the orbit of x.

In Mathlib, z ∈ Gx means ∃ g ∈ G such that g • x = z.

Then Gx = Gy ⟺  exists g ∈ G such that y = g • x.

We now prove this following the definition of group action.
"

open Pointwise
open scoped Pointwise
open scoped MulAction
open MulAction

variable {G X:Type*} [Group G] [MulAction G X]

#check  QuotientGroup.mk_out_eq_mul


Statement (x y : X) :  MulAction.orbit G x = MulAction.orbit G y ↔ ∃ g:G , g • x = y := by
  Hint "Use constrcuctor to split the goal."
  constructor
  · Hint "Introduce the hypothesis."
    intro H
    Hint "Observe that y ∈ Gy. Use `have h1: y ∈ orbit G y` to get the claim and then prove it. You may use `MulAction.one_smul` "
    have h1: y ∈ orbit G y := by
      use 1
      apply MulAction.one_smul
    Hint "Rewrite the goal using {H}. "
    rw [<-H] at h1
    Hint "Now this is exactly {h1}."
    exact h1
  · Hint "Introduce the hypothesis."
    intro H
    Hint "Use  `obtain ⟨g,hg⟩ := H` to deconstruct {H} and get g and the assumption hg on g. "
    obtain ⟨g,hg⟩ := H
    Hint "To prove two sets are equal is to prove z ∈ orbit G x ↔ z ∈ orbit G y. Use `ext z`"
    ext z
    Hint "Now use constructor to decompose the goal"
    constructor
    · Hint "Introduce the hypothesis. Since `simp` is too powerful, try only use `obtain`, `use`, `rw` and `group` to finish the proof. You may need `mul_smul` and apply `beta_redace at *` when necessary. "
      intro hz
      obtain ⟨k,Hk⟩:= hz
      use k * g⁻¹
      beta_reduce at *
      rw [<-hg]
      rw [<-mul_smul]
      rw [<-Hk]
      group
    · intro hz
      obtain ⟨k,Hk⟩:= hz
      use k * g
      beta_reduce at *
      rw [<-Hk]
      rw [<-hg]
      rw [<-mul_smul]

NewTheorem mul_smul MulAction.one_smul Set.range MulAction.orbit
OnlyTactic intro constructor group rw beta_reduce nth_rw obtain ext
