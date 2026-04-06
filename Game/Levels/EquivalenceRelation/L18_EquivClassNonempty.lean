import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 18

Introduction "Every equivalence class is nonempty: given any `c : Setoid.Equivclass α`, there exists some `z ∈ c`. This follows because `c = Setoid.quot z` for some `z`, and we already know `z ∈ Setoid.quot z` (from `Setoid.mem_quot_self`)."

variable {α :Type*} [inst: Setoid α]


Statement  (c : Setoid.Equivclass α ) : ∃ z, z ∈  c := by
  Hint "First, find a representative of `c`. Use `obtain ⟨z, hz⟩ := Setoid.exist_quot c` to get `z : α` and `hz : c = Setoid.quot z`."
  obtain ⟨z, hz⟩ := Setoid.exist_quot c
  Hint "Rewrite the goal using `{hz}` so it becomes `∃ z, z ∈ Setoid.quot z`. Use `rw [{hz}]`."
  rw [hz]
  Hint "Provide the witness `z` for the existential. Use `use z`."
  use z
  Hint "The goal is now `z ∈ Setoid.quot z`, which is `Setoid.mem_quot_self z`. Use `exact Setoid.mem_quot_self z`."
  exact Setoid.mem_quot_self z

Conclusion "Every equivalence class is nonempty. This fact will be needed to define the `unquot` operation, which picks a representative from each class."

NewTheorem Setoid.exist_quot Setoid.mem_quot_self
-- NewTactic moved to BasicLean
OnlyTactic obtain rewrite rw use exact
