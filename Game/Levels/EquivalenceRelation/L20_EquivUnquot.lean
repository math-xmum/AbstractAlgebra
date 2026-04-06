import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 20

Introduction "We introduce `Equivclass.unquot`, which picks a representative element from an equivalence class. Given `c : Setoid.Equivclass α`, `c.unquot : α` is some element belonging to `c`.

In this level we show that taking the quotient of the representative recovers the original class: `Setoid.quot c.unquot = c`. This says that `quot` is a left inverse of `unquot` (up to equality of classes)."

variable {α :Type*} [inst: Setoid α]


Statement (c : Setoid.Equivclass α) : Setoid.quot c.unquot = c := by
  Hint "We want to show `Setoid.quot c.unquot = c`. It is easier to prove `c = Setoid.quot c.unquot` and flip. Use `symm` to swap the sides of the equality."
  symm
  Hint "Now use `rw [<-Setoid.mem_quot_iff_eq_quot]` to convert the goal `c = Setoid.quot c.unquot` into `c.unquot ∈ c`. The `←` (or `<-`) in `rw` applies the rewrite from right to left."
  rw [<-Setoid.mem_quot_iff_eq_quot]
  Hint "The goal is `c.unquot ∈ c`, which is exactly `c.unquot_mem`. This theorem states that the chosen representative belongs to its class. Use `exact c.unquot_mem`."
  exact c.unquot_mem

Conclusion "`Setoid.quot (c.unquot) = c` -- taking the equivalence class of any representative gives back the original class. This is the first half of showing that `quot` and `unquot` are inverses."


NewTheorem Setoid.Equivclass.unquot_mem Setoid.mem_quot_iff_eq_quot
