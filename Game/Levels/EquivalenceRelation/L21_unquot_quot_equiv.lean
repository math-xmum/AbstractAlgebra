import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 21

Introduction "The other direction: if we start with an element `x`, form its equivalence class `Setoid.quot x`, and then pick a representative `(Setoid.quot x).unquot`, the result is equivalent to `x`.

Combined with L20 (`Setoid.quot c.unquot = c`), this shows that `quot` and `unquot` are inverses up to the equivalence relation."

variable {α :Type*} [inst: Setoid α] (c : Setoid.Equivclass α)


Statement (x : α) : x ≈ (Setoid.quot x).unquot := by
  Hint "We need `x ≈ (Setoid.quot x).unquot`. Recall that `Setoid.quot_eq_iff_equiv` says `Setoid.quot x = Setoid.quot y ↔ x ≈ y`. Rewrite backwards to convert the equivalence into an equality of quotients. Use `rw [<-Setoid.quot_eq_iff_equiv]`."
  rw [<-Setoid.quot_eq_iff_equiv]
  Hint "The goal is now `Setoid.quot x = Setoid.quot (Setoid.quot x).unquot`. The theorem `Setoid.Equivclass.quot_unquot_eq` says `Setoid.quot c.unquot = c` for any class `c`. Apply it with `rw [Setoid.Equivclass.quot_unquot_eq]` -- Lean will unify `c` with `Setoid.quot x`."
  rw [Setoid.Equivclass.quot_unquot_eq]

Conclusion "We have `x ≈ (Setoid.quot x).unquot`. This result, `Setoid.unquot_quot_equiv`, completes the round-trip: `quot` followed by `unquot` returns an equivalent element."


NewTheorem Setoid.Equivclass.unquot_mem Setoid.mem_quot_iff_eq_quot Setoid.Equivclass.quot_unquot_eq
