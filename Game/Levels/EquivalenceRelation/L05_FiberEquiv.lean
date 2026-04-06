import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 5


variable {S :Type*}


Introduction "
Given a function $f : S \\to \\beta$, we can define a relation on $S$ by: $x \\sim y$ iff $f(x) = f(y)$. Two elements are related when they map to the same value -- they lie in the same **fiber** of $f$.

This is always an equivalence relation. The proof follows the same pattern as for equality, because we are really just proving that equality (on the codomain, pulled back through $f$) is an equivalence.

New tactic: `exact h.symm` uses dot notation to apply `Eq.symm` to a hypothesis `h : a = b`, producing a proof of `b = a`.
"

Statement (preamble := constructor ) {β : Type*} (f : S → β): Equivalence (α := S) (f · = f ·) := by
  Hint "**Reflexivity.** The goal is `f x = f x`. Use `intro x` then `rfl`."
  intro x
  Hint (hidden := true) "Use `rfl`."
  rfl
  Hint "**Symmetry.** We have `hxy : f x = f y` and need `f y = f x`. Use `intro x y hxy`, then `exact hxy.symm`.

The expression `hxy.symm` applies `Eq.symm` to reverse the equality."
  intro x y hxy
  Hint (hidden := true) "Use `exact {hxy}.symm` to reverse the equality."
  exact hxy.symm
  Hint "**Transitivity.** We have `hxy : f x = f y` and `hyz : f y = f z`, and need `f x = f z`. Use `intro x y z hxy hyz`, then `rw [hxy]` and `exact hyz`."
  intro x y z hxy hyz
  Hint (hidden := true) "Use `rw [{hxy}]` to rewrite, then `exact {hyz}`."
  rw [hxy]
  Hint (hidden := true) "Use `exact {hyz}`."
  exact hyz

-- NewTactic moved to BasicLean
OnlyTactic intro rfl rw exact unfold
