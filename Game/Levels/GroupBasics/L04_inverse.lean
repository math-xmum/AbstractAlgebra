import Game.Metadata
-- import Mathlib

World "GroupBasics"

Level 4

Title "Existence of Inverses"

Introduction "
A  monoid is a semi-group with identity and .

A  group is a monoid such that every element has inverse.
"

variable (G :Type*) [Group G]

Introduction "The following statement claims that in a group, for any element $a$, there exists an element $b$ such that $a \\cdot b = 1$ and $b \\cdot a = 1$. This is essentially proving the existence of an inverse element for any group element."

Statement (a: G) : ∃ (b:G), (a*b =1 ∧ b*a = 1) := by
  Hint "To solve this problem, we need to find an element that serves as the inverse of {a}. In a group, every element has an inverse, denoted as `a⁻¹`."
  use a⁻¹
  Hint "Now we need to prove that {a} * {a}⁻¹ = 1 and {a}⁻¹ * {a} = 1. We can split this conjunction into two separate goals using `apply And.intro`."
  apply And.intro
  Hint "For the first goal, we need to show that {a} * {a}⁻¹ = 1. The `group` tactic can solve this automatically since it knows the properties of groups."
  · group
  Hint "For the second goal, we need to show that {a}⁻¹ * {a} = 1. Again, the `group` tactic can solve this."
  · group



Conclusion "Every element in a group has an inverse. We used `And.intro` to split a conjunction into two goals."

NewTheorem And.intro
