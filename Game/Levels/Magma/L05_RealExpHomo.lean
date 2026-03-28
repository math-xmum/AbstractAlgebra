
import Game.Metadata
import Game.Levels.Lemmas.Group
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

World "Magma"

Level 5

Introduction "The following statement claims that the exponential function $Real.exp$ is a multiplicative homomorphism with respect to addition. In other words, $exp(a + b) = exp(a) * exp(b)$ for all real numbers $a$ and $b$."

Statement : Mul.isAddMulMap Real.exp := by
  Hint "Fortunately, this property is already proven in the library as `Real.exp_add`."
  exact Real.exp_add

NewDefinition Mul.isAddMulMap
NewTheorem Real.exp_add
OnlyTheorem Real.exp_add
