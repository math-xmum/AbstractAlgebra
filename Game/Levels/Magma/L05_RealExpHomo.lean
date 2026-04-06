
import Game.Metadata
import Game.Levels.Lemmas.Group

World "Magma"

Level 5

Introduction "
The real exponential function $\\exp : \\mathbb{R} \\to \\mathbb{R}$ converts the binary operation
of **addition** ($+$) into the binary operation of **multiplication** ($\\times$):
$\\exp(a + b) = \\exp(a) \\cdot \\exp(b)$.

This makes $\\exp$ a magma homomorphism from $(\\mathbb{R}, +)$ to $(\\mathbb{R}, \\times)$.
The definition `Mul.isAddMulMap f` says exactly $f(a + b) = f(a) * f(b)$ for all $a, b$.

This fact is already in Mathlib as `Real.exp_add`. Since the goal matches this theorem
exactly, one tactic suffices.
"

Statement : Mul.isAddMulMap Real.exp := by
  Hint "The goal matches the theorem `Real.exp_add` exactly. Use `exact Real.exp_add` to close the proof in one step."
  exact Real.exp_add

NewDefinition Mul.isAddMulMap
NewTheorem Real.exp_add
OnlyTheorem Real.exp_add
