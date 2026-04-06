
import Game.Metadata
import Game.Levels.Lemmas.Group

World "Magma"

Level 4

Introduction "
A **magma homomorphism** is a function between two magmas that preserves the binary operation.
Given magmas $(A, *)$ and $(B, \\cdot)$, a function $f : A \\to B$ is a homomorphism if
$f(a * b) = f(a) \\cdot f(b)$ for all $a, b$.

Here both the domain and codomain are $(\\mathbb{N}, \\times)$ -- the natural numbers under
**multiplication**. The definition `Mul.isMulMap f` says exactly that
$f(x * y) = f(x) * f(y)$ for all $x, y$.

We prove that $f(x) = x \\cdot x$ is a multiplicative homomorphism on $\\mathbb{N}$.
The key tools are `Nat.mul_assoc` and `Nat.mul_comm`.
"

Statement: Mul.isMulMap (fun (x :ℕ) => x * x) := by
  Hint "Start by expanding the definition. Use `unfold Mul.isMulMap` to see the homomorphism condition explicitly."
  unfold Mul.isMulMap

  Hint "The goal contains anonymous function applications like `(fun x => x * x) a`. The tactic `beta_reduce` evaluates these, replacing them with `a * a`. Use `beta_reduce`."
  beta_reduce

  Hint "The goal is now `∀ x y, (x * y) * (x * y) = (x * x) * (y * y)`. Use `intro x y` to fix two arbitrary natural numbers."
  intro x y

  Hint "We need to rearrange `(x * y) * (x * y)` into `(x * x) * (y * y)` using associativity and commutativity. First, use `rw [Nat.mul_assoc x y (x * y)]` to re-associate the left side as `x * (y * (x * y))`."
  rw [Nat.mul_assoc x y (x * y)]

  Hint "Now swap `y * (x * y)` to `(x * y) * y` using `rw [Nat.mul_comm y (x*y)]`."
  rw [Nat.mul_comm y (x*y)]

  Hint "Re-associate `(x * y) * y` into `x * (y * y)` using `rw [Nat.mul_assoc x y y]`."
  rw [Nat.mul_assoc x y y]

  Hint "Finally, use `rw [<-Nat.mul_assoc x x (y*y)]` to group `x * (x * (y * y))` as `(x * x) * (y * y)`, matching the right side exactly."
  rw [<-Nat.mul_assoc x x (y*y)]


-- NewTactic moved to BasicLean
OnlyTactic unfold beta_reduce intro rw
NewTheorem Nat.mul_assoc Nat.mul_comm
OnlyTheorem Nat.mul_assoc Nat.mul_comm
NewDefinition Mul.isMulMap
OnlyDefinition Mul.isMulMap
