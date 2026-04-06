import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 4

Introduction "Recall the algebraic hierarchy: a **monoid** is a semigroup with an identity element, and a **group** is a monoid where every element has an inverse.

In this level, we prove that for any element $a$ in a group, there exists $b$ such that $a \\cdot b = 1$ and $b \\cdot a = 1$. The natural candidate is $b = a^{-1}$.

New tactics:
- `use e` : provides a witness `e` for an existential goal `\\exists x, P x`.
- `apply And.intro` : splits a conjunction goal `P \\wedge Q` into two separate subgoals."

variable (G :Type*) [Group G]

Statement (a: G) : ∃ (b:G), (a*b =1 ∧ b*a = 1) := by
  Hint "The goal is `∃ b, a * b = 1 ∧ b * a = 1`. We need to provide a witness. Use `use a⁻¹` to propose `a⁻¹` as the inverse."
  use a⁻¹
  Hint "Now the goal is `{a} * {a}⁻¹ = 1 ∧ {a}⁻¹ * {a} = 1`. Use `apply And.intro` to split this into two subgoals."
  apply And.intro
  Hint "The first subgoal is `{a} * {a}⁻¹ = 1`. The `group` tactic solves equations that follow from group axioms."
  · group
  Hint "The second subgoal is `{a}⁻¹ * {a} = 1`. Again, `group` handles this."
  · group



NewTheorem And.intro
