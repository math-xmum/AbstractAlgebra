import Game.Metadata

World "BasicGroupTheory"
Level 3

Title "Inverse Uniqueness"

Introduction "In this third level the goal is to prove the left inverse of an element is unique.

That is `∀ y : G, y * x = 1 → y = x⁻¹`.

In order to prove a universal proposition, we need to use the tactic `intro`."

Statement (G : Type*) [Group G] (x : G) : ∀ y : G, y * x = 1 → y = x⁻¹ := by
  Hint "Try to execute `intro y h`. We can get an assumption `h` saying that `y * x = 1`, while `y` is arbitrary."
  intro y h
  Hint "Then to prove `y = x⁻¹`, we need to rewrite the proof `h` with lemmas on the right.

  You can click on lemmas to learn their specific content and usage.

  `←` is useful in this level, `← h` means switching the two sides of the equation in `h`.

  Type \\l and then hit the space bar can get this arrow.

  For example, You can execute `rw [← h]`, if you want to rewrite the proof `1 = y * x` rather than `h : y * x = 1`."
  Hint "Similarly, `← one_mul` means `(a : G): a = 1 * a`.

  Let's learn how to tell Lean to change `x⁻¹` in the goal `y = x⁻¹` by giving `← one_mul` an explicit parameter.

  Try `rw [← one_mul x⁻¹]` to change `x⁻¹` into `1 * x⁻¹`."
  rw [← one_mul x⁻¹]
  Hint "Can you take it from here?"
  Hint (hidden := true) "Try `rw [← h, mul_assoc, mul_inv_cancel, mul_one]`"
  rw [← h]
  rw [mul_assoc]
  rw [mul_inv_cancel]
  rw [mul_one]

Conclusion "Level completed! Let's continue the journey."

/- Use these commands to add items to the game's inventory. -/

NewTheorem one_mul mul_assoc mul_inv_cancel mul_one
-- NewDefinition Nat Add Eq
