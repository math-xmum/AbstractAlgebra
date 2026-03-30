import Game.Metadata

World "EquivalenceRelation"
Level 1

Title "Equality is an Equivalence Relation"

Introduction "An equivalence relation on a type is a binary relation that is reflexive, symmetric, and transitive. Reflexive means every element is related to itself. Symmetric means if a is related to b, then b is related to a. Transitive means if a is related to b and b is related to c, then a is related to c. Equality is the simplest example of an equivalence relation, and we will prove this now."

Statement (preamble := constructor) {α : Type*} : Equivalence (α := α) (· = ·) := by
  Hint "We need to prove reflexivity: for every x, x = x. Use `intro x` to introduce the variable, then `rfl` to close the goal."
  intro x
  rfl
  Hint "Now we prove symmetry: if x = y then y = x. Use `intro x y hxy` to introduce the variables and hypothesis."
  intro x y hxy
  Hint "We can rewrite using the hypothesis {hxy}. Try `rw [hxy]`."
  rw [hxy]
  Hint "Now we prove transitivity: if x = y and y = z then x = z. Use `intro x y z hxy hyz`."
  intro x y z hxy hyz
  Hint "Rewrite using {hxy} and then use `exact {hyz}`."
  rw [hxy]
  exact hyz

Conclusion "We have shown equality satisfies all three properties: reflexivity, symmetry, and transitivity."

NewTactic intro rfl rw exact
