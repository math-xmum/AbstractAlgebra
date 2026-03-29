import Game.Metadata

World "GroupBasics"
Level 1

Title "mul_assoc"

Introduction "The next levels focus on the basic properties required in the definition of group.

In this second level the goal is `a * b * c = b * (a * c)`, but to help us we have an assumption `h` saying that `a * b = b * a`.

Check that you can see `h` in your list of assumptions.
Before we can use `rfl`, we have to substitute `b * a` for `a * b`.

We do this in Lean by rewriting the proof `h`, using the `rw` tactic."

Statement (G : Type*) [Group G] (a b c : G) (h : a * b = b * a) : a * b * c = b * (a * c) := by
  Hint "First execute `rw [h]` to replace the `a * b` with `b * a`."
  rw [h]
  Hint "Then recall the definition of group in level 1, we know that `(a b c : G): a * b * c = a* (b * c)`.

  The proof of `a * b * c = a * (b * c)` is called mul_assoc."
  -- Check out the "Lemma" tab in the list of lemmas on the right for this and other proofs.
  Hint "Continue with `rw [mul_assoc]` to change `b * a * c`  to `b * (a * c)`. Lean can automatically identify variables to apply the lemmas."
  rw [mul_assoc]

Conclusion "Level completed! Note that you can do `rw [h, mul_assoc]` to solve this level in one line.

Let's continue the journey."

/- Use these commands to add items to the game's inventory. -/

NewTheorem mul_assoc
-- NewDefinition Nat Add Eq
