import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 12

Title "The Descent Lemma"

Introduction "The descent lemma says: if a function f : α → β respects the equivalence relation (meaning f(a) = f(b) whenever a ≈ b), then f 'descends' to a well-defined function f̄ on the quotient α/≈, and f = f̄ ∘ quot. This is the universal property of quotients — any compatible function factors through the quotient."

variable {α : Type*} [Setoid α]

Statement (β : Type*) (f : α → β) (H : ∀ a b, a ≈ b → f a = f b) :
    let fbar : Setoid.Equivclass α → β := fun c => f c.unquot
    ∀ x, f x = fbar (Setoid.quot x) := by
  Hint "The `let` binding `fbar` is already in the context. Introduce the universally quantified variable `x` using `intro x`."
  intro x
  Hint "The goal is `f x = f (Setoid.quot x).unquot`. Apply the hypothesis `H` — we need to show that `x ≈ (Setoid.quot x).unquot`."
  apply H
  exact Setoid.unquot_quot_equiv

Conclusion "This completes our study of equivalence relations. The descent lemma is the key tool for constructing functions on quotient structures, which we will use when defining quotient groups."

NewTheorem Setoid.unquot_quot_equiv
OnlyTactic intro apply exact
