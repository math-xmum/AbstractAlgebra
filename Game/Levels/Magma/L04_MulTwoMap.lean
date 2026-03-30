
import Game.Metadata
import Game.Levels.Lemmas.Group

World "Magma"

Level 4
Title "Squaring is a homomorphism"

Introduction "The following statement claims that the function $f(x) = x^2$ (or $x * x$ in Lean notation) is a multiplication homomorphism. In other words, for any two natural numbers $x$ and $y$, $f(x * y) = f(x) * f(y)$."

Statement: Mul.isMulMap (fun (x :ℕ) => x * x) := by
  Hint "We need to unfold the definition of `Mul.isMulMap` to see what we need to prove. Use `unfold Mul.isMulMap`."
  unfold Mul.isMulMap

  Hint "Now we need to simplify the anonymous function applications. Use `beta_reduce` to evaluate the function applications."
  beta_reduce

  Hint "We need to prove that for all natural numbers $x$ and $y$, $(x * y) * (x * y) = (x * x) * (y *y)$. Let's introduce these variables with `intro x y`."
  intro x y

  Hint "Now we need to manipulate the left side of the equation to match the right side. Let's use the associativity of multiplication. Use `rw [Nat.mul_assoc x y (x * y)]`."
  rw [Nat.mul_assoc x y (x * y)]

  Hint "We can use the commutativity of multiplication to reorder the terms. "
  rw [Nat.mul_comm y (x*y)]

  Hint "Apply associativity again to group the terms properly. "
  rw [Nat.mul_assoc x y y]

  Hint "Finally, we can use associativity one more time to match the right side exactly. "
  rw [<-Nat.mul_assoc x x (y*y)]


Conclusion "You proved that x ↦ x² preserves multiplication on ℕ. This is your first example of a magma homomorphism — a map that respects the binary operation."

NewTactic unfold beta_reduce intro rw
OnlyTactic unfold beta_reduce intro rw
NewTheorem Nat.mul_assoc Nat.mul_comm
OnlyTheorem Nat.mul_assoc Nat.mul_comm
NewDefinition Mul.isMulMap
OnlyDefinition Mul.isMulMap
