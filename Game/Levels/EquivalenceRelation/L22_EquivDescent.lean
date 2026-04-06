import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 22

Introduction "This is the **descent** (or universal) property of quotients. Given a function `f : α → β` that respects the equivalence relation (meaning `a ≈ b → f a = f b`), we can define a function `fbar` on equivalence classes by `fbar c = f c.unquot`.

The key claim is that `fbar` is compatible with `f`: for every `x : α`, we have `f x = fbar (Setoid.quot x)`. This says the diagram commutes: applying `f` directly gives the same result as first passing to the quotient and then applying `fbar`."

variable {α :Type*} [inst: Setoid α]

variable (c : Setoid.Equivclass α)

--#check c.unquot

Statement {β : Type*} (f : α → β) (H: ∀ a b, a ≈ b → f a = f b):
  let fbar :Setoid.Equivclass α → β := fun c => f c.unquot
  ∀ x, f x = fbar (Setoid.quot x)
  := by
  Hint "The goal is `∀ x, f x = fbar (Setoid.quot x)`. Start by introducing an arbitrary `x`. Use `intro x`."
  intro x
  Hint "Lean needs to unfold the local definition of `fbar`. Use `simp [fbar]` to simplify `fbar (Setoid.quot x)` into `f (Setoid.quot x).unquot`."
  simp only [fbar]
  Hint "The goal is now `f x = f (Setoid.quot x).unquot`. Since `f` respects the equivalence relation (hypothesis `H`), it suffices to show `x ≈ (Setoid.quot x).unquot`. Use `apply H` to reduce the goal to proving this equivalence."
  apply H
  Hint "The goal is `x ≈ (Setoid.quot x).unquot`, which is exactly `Setoid.unquot_quot_equiv` from the previous level. Use `exact Setoid.unquot_quot_equiv`."
  exact Setoid.unquot_quot_equiv

Conclusion "This completes the descent property. Any function that respects the equivalence relation factors through the quotient. This is the universal property of quotient sets -- one of the most important constructions in algebra."

NewTheorem Setoid.unquot_quot_equiv
