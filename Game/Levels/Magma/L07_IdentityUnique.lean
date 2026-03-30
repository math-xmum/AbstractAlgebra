import Game.Metadata
import Game.Levels.Lemmas.Group
-- import Mathlib

World "Magma"

Level 7
Title "Identity element is unique"

Introduction "
Suppose $G$ is a set with a binary operation $*$.

The following statement claims that identity element is unique.

Suppose $e$ and $e'$ are two identity elements, we need to prove $e=e'$.
"

variable (α :Type*) [Mul α]


Introduction "This statement proves the uniqueness of the identity element in a group. It shows that if both $e$ and $e'$ satisfy the properties of an identity element (left and right multiplication), then they must be equal."

open Mul

Introduction "The following statement claims that in a multiplicative structure, if $e$ and $e'$ are both identity elements, then they must be equal. This is a fundamental result showing that identity elements are unique."



Statement (e e' : α) (he: Mul.isIdentity e) (he': Mul.isIdentity e') : e = e' := by
  Hint "First, let's unfold the definition of `Mul.isIdentity` to see what we're working with. You can use `unfold Mul.isIdentity at *`."
  unfold Mul.isIdentity at *

  Hint "Now we have {he} and {he'} which tell us that $e$ and $e'$ are identity elements. Let's specialize {he} to the element $e'$. You can use `specialize {he} e'`."
  Hint "The tactic specialize h a₁ ... aₙ works on local hypothesis h. The premises of this hypothesis, either universal quantifications or non-dependent implications, are instantiated by concrete terms coming from arguments a₁ ... aₙ. The tactic adds a new hypothesis with the same name h := h a₁ ... aₙ and tries to clear the previous one."
  specialize he e'

  Hint "We now have {he} which says $e' * e = e'$ and $e * e' = e'$. Let's rewrite our goal using the first part. You can use `rw [<- {he}.1]`."
  rw [<- he.1]

  Hint "Now we need to show that $e = e' * e$. Let's specialize {he'} to the element $e$. You can use `specialize {he'} e`."
  specialize he' e

  Hint "Finally, we have {he'} which says $e' * e = e$. We can use this to complete the proof by rewriting with the second component of {he'}. You can use `rw [{he'}.2]`."
  rw [he'.2]

Conclusion "Note: The proof doesn't actually use the second claim of `he` or the first claim of `he'`, but they're part of the symmetric definition of identity elements.
"

NewDefinition Mul.isIdentity MulEquiv.apply_symm_apply
OnlyTactic unfold rw sepcialize
