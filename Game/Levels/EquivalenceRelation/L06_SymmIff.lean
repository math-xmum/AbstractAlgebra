import Game.Metadata

World "EquivalenceRelation"
Level 6

Title "Symmetry of Equivalence Relations"

Introduction "Now we work with an abstract equivalence relation on a type, formalized as a Setoid in Lean. A Setoid on a type provides a relation denoted x ~ y (written x ≈ y in Lean). The first basic property we verify is that x ≈ y if and only if y ≈ x. This is simply the symmetry property stated as a biconditional."

variable {α : Type*} [Setoid α]

Statement {x y : α} : x ≈ y ↔ y ≈ x := by
  Hint "We need to prove an if-and-only-if. Use `constructor` to split into the two directions."
  constructor
  Hint "For the forward direction, we need to show x ≈ y implies y ≈ x. Use `exact Setoid.symm`."
  exact Setoid.symm
  Hint "For the backward direction, we again use symmetry. Use `exact Setoid.symm`."
  exact Setoid.symm

Conclusion "Symmetry as a biconditional is a simple but useful reformulation. It lets us freely swap the two sides of an equivalence relation in any proof."

NewTactic constructor
NewTheorem Setoid.symm
