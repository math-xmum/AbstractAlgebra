import Game.Metadata
-- import Mathlib

World "GroupBasics"

Level 2

Title "Associativity in Semigroups"

Introduction "
A semi-group is a set $G$ with a binary operation $*$ such that $*$ has associative law.
"

variable (G :Type*) [Semigroup G]


Statement (a b c : G) : (a * b) * c = a * (b * c)  := by
  Hint "Use `group`"
  group

Conclusion "The `group` tactic handles associativity and other group equations automatically."

NewTactic  group
