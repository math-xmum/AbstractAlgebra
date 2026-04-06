import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 2

Introduction "A **semigroup** is a set $G$ with an associative binary operation $*$. That is, $(a * b) * c = a * (b * c)$ for all $a, b, c \\in G$.

Every group is a semigroup (groups have additional axioms: identity and inverses). In this level, we prove associativity directly using the `group` tactic.

The `group` tactic automatically solves equations that follow from the group axioms. It handles associativity, identity, and inverse cancellations."

variable (G :Type*) [Semigroup G]


Statement (a b c : G) : (a * b) * c = a * (b * c)  := by
  Hint "The goal `(a * b) * c = a * (b * c)` is a direct consequence of the semigroup axiom. Use the `group` tactic to close it automatically."
  group

-- NewTactic moved to BasicLean
