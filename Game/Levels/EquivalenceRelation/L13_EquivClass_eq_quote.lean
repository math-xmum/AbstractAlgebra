import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 13

Introduction "Every equivalence class `c : Setoid.Equivclass α` is, by definition, a set that equals `Setoid.quot x` for some element `x`. In this level we extract that witness: we prove `∃ x, c = Setoid.quot x`.

Since `Setoid.Equivclass α` is a subtype `{c : Set α // ∃ x, c = {y | x ≈ y}}`, the witness is already hiding inside `c`."

variable {α :Type*} [inst: Setoid α]


Statement (c : Setoid.Equivclass α) : ∃ x, c = Setoid.quot x  := by
  Hint "The term `c` is a subtype: it consists of a set together with a proof that the set is an equivalence class. Use `obtain ⟨c, x, hx⟩ := c` to destructure it into the underlying set `c`, a representative `x`, and a proof `hx` that the set is the equivalence class of `x`. The `obtain` tactic pattern-matches on structured data."
  obtain ⟨c, x, hx⟩ := c
  Hint "Now provide the witness `x` for the existential using `use x`. The `use` tactic supplies a witness for an `∃` goal."
  use x
  Hint "Unfold `Setoid.quot` so both sides use the same raw set definition."
  unfold Setoid.quot
  Hint "The goal now follows from `{hx}`. Use `simp only [{hx}]` to rewrite and close the goal."
  simp only [hx]

Conclusion "We have shown that every equivalence class has a representative element."

NewDefinition Setoid.quot
-- NewTactic moved to BasicLean
OnlyTactic obtain use unfold rfl simp exact
