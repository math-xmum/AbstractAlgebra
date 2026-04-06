import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 9

Introduction "The **commutator** of two group elements $a$ and $b$ is defined as $[a, b] := a \\cdot b \\cdot a^{-1} \\cdot b^{-1}$. It measures how much $a$ and $b$ fail to commute: $a \\cdot b = b \\cdot a$ if and only if $[a, b] = 1$.

In this level, we prove this equivalence. The forward direction uses rewriting and `group`. The reverse direction uses `mul_right_cancel`, which states: if $a \\cdot c = b \\cdot c$ then $a = b$. We apply it twice to strip inverses from both sides."


variable {G : Type*} [Group G]

open Group Monoid

Statement {a b: G} : a * b = b * a ↔  a * b * a⁻¹* b⁻¹=1  := by
  Hint "The goal is an `↔` (if and only if). Use `constructor` to split it into two implications."
  constructor
  · intro H
    Hint "Use `rw [H]` to replace `a * b` with `b * a` in the goal."
    rw [H]
    Hint "The goal is now `b * a * a⁻¹ * b⁻¹ = 1`. Use `group` to simplify and close it."
    group
  · intro H
    Hint "We need `a * b = b * a` from `H : a * b * a⁻¹ * b⁻¹ = 1`. Use `mul_right_cancel` twice to cancel inverses. Try `apply mul_right_cancel (b := a⁻¹)` then `apply mul_right_cancel (b := b⁻¹)`."
    apply mul_right_cancel (b := a⁻¹)
    apply mul_right_cancel (b := b⁻¹)
    Hint "Now rewrite the left side using `rw [H]` to substitute the commutator equation."
    rw [H]
    Hint "Use `group` to finish the remaining algebraic simplification."
    group


#check mul_right_cancel

NewTheorem mul_right_cancel mul_left_cancel mul_right_cancel_iff
mul_right_cancel_iff commutatorElement_def
