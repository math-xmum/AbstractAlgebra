import Game.Metadata

World "BasicGroupTheory"
Level 3

Title "Inverse Uniqueness"

Introduction "In a group, every element $x$ has a unique inverse $x^{-1}$. This level proves that if $y \\cdot x = 1$, then $y = x^{-1}$. In other words, any left inverse of $x$ must equal the standard inverse $x^{-1}$.

The goal is a universally quantified implication: `∀ y : G, y * x = 1 → y = x⁻¹`. To prove it, we use `intro` to introduce the variable `y` and the hypothesis into context, then rewrite using group axioms:
- `one_mul` : `1 * a = a`
- `mul_assoc` : `a * b * c = a * (b * c)`
- `mul_inv_cancel` : `a * a⁻¹ = 1`
- `mul_one` : `a * 1 = a`"

Statement (G : Type*) [Group G] (x : G) : ∀ y : G, y * x = 1 → y = x⁻¹ := by
  Hint "The goal starts with `∀ y : G, y * x = 1 → ...`. Use `intro y h` to introduce the variable `y` and the hypothesis `h : y * x = 1` into context."
  intro y h
  Hint "We want to show `y = x⁻¹`. The strategy is to multiply both sides by suitable terms. First, rewrite `x⁻¹` as `1 * x⁻¹` using `← one_mul`.

  The `←` (typed `\\l` then space) reverses a rewrite: `rw [← one_mul x⁻¹]` rewrites `x⁻¹` to `1 * x⁻¹`. We pass the explicit argument `x⁻¹` so Lean knows where to apply it."
  rw [← one_mul x⁻¹]
  Hint "Now the goal is `y = 1 * x⁻¹`. Replace `1` with `y * x` using `rw [← h]`, then use `mul_assoc`, `mul_inv_cancel`, and `mul_one` to finish."
  Hint (hidden := true) "Complete solution from here: `rw [← h, mul_assoc, mul_inv_cancel, mul_one]`"
  rw [← h]
  rw [mul_assoc]
  rw [mul_inv_cancel]
  rw [mul_one]

Conclusion "Well done! You proved that any left inverse equals the standard inverse. The chain of rewrites was:
`y = 1 * x⁻¹ = (y * x) * x⁻¹ = y * (x * x⁻¹) = y * 1 = y`. Since both sides equal `y`, the equality holds."

/- Use these commands to add items to the game's inventory. -/

NewTheorem one_mul mul_assoc mul_inv_cancel mul_one
-- NewDefinition Nat Add Eq
