import Game.Metadata
import Game.Levels.Lemmas.Group
-- import Mathlib

World "Magma"

Level 8


variable (α β:Type*) [Mul α] [Mul β]


Introduction "The following statement claims that if $e$ is a multiplicative identity in a structure $α$, then its image under a multiplicative equivalence $φ$ is also a multiplicative identity in the structure $β$. This is a fundamental property of multiplicative equivalences, showing that they preserve multiplicative identities."

Statement (e : α) (he: Mul.isIdentity e) (φ : α ≃* β): Mul.isIdentity (φ e) := by
  Hint "Let's start by unfolding the definition of `Mul.isIdentity` to see what we need to prove."
  unfold Mul.isIdentity at he
  Hint "We need to prove that for any element $x'$ in $β$, both $x' * φ (e) = x'$ and $φ(e) * x' = x'$. Let's introduce $x'$."
  intro x'
  Hint "To use our hypothesis {he}, we need to relate $x'$ in $β$ to some element in $α$. Note that φ is an isomorphism, the inverse of φ is called `{φ}.symm` in Mathlib. Let's define $y$ as the image of $x'$ under {φ}.symm. Use `let y := φ.symm x'`"
  let y := φ.symm x'
  Hint "Now we need to establish the relationship between $x'$ and $φ(y)$. By definition of the inverse of an equivalence, we have $x' = φ(y)$. One can use `have hx' : φ (y) = x' := MulEquiv.apply_symm_apply _ _`"
  have hx' : φ (y) = x' := MulEquiv.apply_symm_apply _ _
  Hint "Let's substitute $x'$ with $φ(y)$ in our goal. Then use `specialize he y` and `constructor` to split into two cases."
  rw [←hx']
  specialize he y
  constructor
  Hint "Use `rw [← MulEquiv.map_mul]` to pull the multiplication inside {φ}, then rewrite with the identity law."
  rw [← MulEquiv.map_mul, he.1]
  Hint "Same idea for the right identity."
  rw [← MulEquiv.map_mul, he.2]


NewTactic apply_fun unfold rw sepcialize «let»
OnlyTactic unfold rw sepcialize «let»
NewTheorem Mul.isIdentity MulEquiv.apply_symm_apply MulEquiv.map_mul
OnlyTheorem Mul.isIdentity MulEquiv.apply_symm_apply MulEquiv.map_mul
