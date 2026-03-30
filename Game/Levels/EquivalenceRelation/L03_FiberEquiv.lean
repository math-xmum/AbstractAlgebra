import Game.Metadata

World "EquivalenceRelation"
Level 3

Title "Fiber Equivalence"

Introduction "Given a function f : S -> B, we can define a relation on S by saying a ~ b if f(a) = f(b). This is always an equivalence relation. The equivalence classes are exactly the fibers (preimages of single points) of f. This construction shows that every function naturally induces an equivalence relation on its domain."

Statement (preamble := constructor) {S : Type*} (β : Type*) (f : S → β) : Equivalence (α := S) (f · = f ·) := by
  Hint "For reflexivity, we need f(x) = f(x) for all x. Use `intro x` then `rfl`."
  intro x
  rfl
  Hint "For symmetry, if f(x) = f(y) then f(y) = f(x). Use `intro x y hxy` then `exact hxy.symm`."
  intro x y hxy
  exact hxy.symm
  Hint "For transitivity, if f(x) = f(y) and f(y) = f(z), then f(x) = f(z). Use `intro x y z hxy hyz`, then rewrite with `hxy` and close with `exact hyz`."
  intro x y z hxy hyz
  rw [hxy]
  exact hyz

Conclusion "Any function gives rise to an equivalence relation via its fibers. This is a fundamental connection between functions and equivalence relations."

NewTactic intro rfl rw exact
