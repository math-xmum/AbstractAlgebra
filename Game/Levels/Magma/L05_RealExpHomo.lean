
import Game.Metadata
import Game.Levels.Lemmas.Group
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

World "Magma"

Level 5
Title "Exp is an additive-multiplicative map"

Introduction "The following statement claims that the exponential function $Real.exp$ is a multiplicative homomorphism with respect to addition. In other words, $exp(a + b) = exp(a) * exp(b)$ for all real numbers $a$ and $b$."

Statement : Mul.isAddMulMap Real.exp := by
  Hint "Fortunately, this property is already proven in the library as `Real.exp_add`."
  exact Real.exp_add

Conclusion "The exponential function sends addition to multiplication: exp(a+b) = exp(a)·exp(b). This makes exp a homomorphism from (ℝ,+) to (ℝ,×)."

NewDefinition Mul.isAddMulMap
NewTheorem Real.exp_add
OnlyTheorem Real.exp_add
