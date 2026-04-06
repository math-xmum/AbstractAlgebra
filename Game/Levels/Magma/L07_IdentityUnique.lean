import Game.Metadata
import Game.Levels.Lemmas.Group
-- import Mathlib

World "Magma"

Level 7

Introduction "
Suppose $(G, *)$ is a magma under **multiplication**. An element $e \\in G$ is an
**identity element** if $x * e = x$ and $e * x = x$ for every $x \\in G$.
The definition `Mul.isIdentity e` encodes exactly this.

We prove that the identity element is **unique**: if both $e$ and $e'$ are identity
elements, then $e = e'$.

The key idea is to evaluate the product $e' * e$ in two ways. The tactic `specialize`
instantiates a universally quantified hypothesis with a concrete value.
For example, `specialize h a` replaces `h : ∀ x, P x` with `h : P a`.
"

variable (α :Type*) [Mul α]


open Mul



Statement (e e' : α) (he: Mul.isIdentity e) (he': Mul.isIdentity e') : e = e' := by
  Hint "Start by expanding the definition of `Mul.isIdentity` in all hypotheses. Use `unfold Mul.isIdentity at *` -- the `at *` means 'apply everywhere'."
  unfold Mul.isIdentity at *

  Hint "Now `{he}` says `∀ x, x * e = x ∧ e * x = x`, and similarly for `{he'}`. Use `specialize {he} e'` to instantiate `{he}` with $e'$, giving `e' * e = e' ∧ e * e' = e'`."
  specialize he e'

  Hint "From `{he}` we know `e' * e = e'` (the `.1` component). Rewrite the goal `e = e'` backwards: use `rw [<- {he}.1]` to change the goal to `e = e' * e`."
  rw [<- he.1]

  Hint "Now we need `e = e' * e`. Use `specialize {he'} e` to get `e * e' = e ∧ e' * e = e`."
  specialize he' e

  Hint "The `.2` component of `{he'}` gives `e' * e = e`. Use `rw [{he'}.2]` to rewrite the goal, making both sides equal and closing the proof."
  rw [he'.2]

Conclusion "Note: we only used `he.1` (that $e' * e = e'$) and `he'.2` (that $e' * e = e$). The other halves were not needed, but they are part of the symmetric definition of an identity element."

NewDefinition Mul.isIdentity MulEquiv.apply_symm_apply
OnlyTactic unfold rw sepcialize
