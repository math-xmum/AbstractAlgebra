import Game.Metadata
import Game.Levels.Lemmas.Group
-- import Mathlib

World "Magma"

Level 8


variable (α β:Type*) [Mul α] [Mul β]


Introduction "
A **multiplicative equivalence** (written `α ≃* β` in Lean) is a bijection between two
magmas under **multiplication** that preserves the operation: $\\varphi(a * b) = \\varphi(a) * \\varphi(b)$.

We prove that such an equivalence preserves identity elements: if $e$ is an identity in
$(\\alpha, *)$, then $\\varphi(e)$ is an identity in $(\\beta, *)$.

Key tools: `MulEquiv.map_mul` (the homomorphism property), `MulEquiv.apply_symm_apply`
(applying $\\varphi$ then $\\varphi^{-1}$ gives the original element), and the `let` tactic
for introducing local definitions.
"

Statement (e : α) (he: Mul.isIdentity e) (φ : α ≃* β): Mul.isIdentity (φ e) := by
  Hint "Use `unfold Mul.isIdentity at he` to expand the identity definition in hypothesis `he`, revealing that $x * e = x$ and $e * x = x$ for all $x$."
  unfold Mul.isIdentity at he
  Hint "The goal asks us to show `Mul.isIdentity (φ e)`, which means for all $x' \\in \\beta$, $x' * \\varphi(e) = x'$ and $\\varphi(e) * x' = x'$. Use `intro x'` to fix an arbitrary element."
  intro x'
  Hint "Our hypothesis `{he}` works in $\\alpha$, but `x'` lives in $\\beta$. Since $\\varphi$ is an equivalence, its inverse `{φ}.symm` maps $\\beta \\to \\alpha$. Use `let y := φ.symm x'` to define the preimage of `x'`. The `let` tactic introduces a local definition into the context."
  let y := φ.symm x'
  Hint "We need the fact that $\\varphi(y) = x'$, i.e., applying $\\varphi$ to its inverse on $x'$ recovers $x'$. Use `have hx' : φ (y) = x' := MulEquiv.apply_symm_apply _ _`. The `have` tactic introduces a new hypothesis with a proof."
  have hx' : φ (y) = x' := MulEquiv.apply_symm_apply _ _
  Hint "Now rewrite `x'` as `φ y` in the goal using `rw [<-hx']`."
  rw [<-hx']
  Hint "Now instantiate `{he}` with `y` using `specialize he y`, giving us `y * e = y ∧ e * y = y`."
  specialize he y
  Hint "The goal is a conjunction `_ ∧ _`. Use `constructor` to split it into two subgoals."
  constructor
  Hint "We want `φ y * φ e = φ y`. Since $\\varphi$ preserves multiplication, `MulEquiv.map_mul` gives `φ (a * b) = φ a * φ b`. Rewrite backwards with `rw [<- MulEquiv.map_mul]` to get `φ (y * e) = φ y`."
  rw [<- MulEquiv.map_mul]
  Hint "Now use `rw [he.1]` to replace `y * e` with `y` (from the first part of `{he}`), making both sides `φ y`."
  rw [he.1]
  Hint "For the second subgoal `φ e * φ y = φ y`, again use `rw [<- MulEquiv.map_mul]` to pull the multiplication inside $\\varphi$."
  rw [<- MulEquiv.map_mul]
  Hint "Use `rw [he.2]` to replace `e * y` with `y` (from the second part of `{he}`), completing the proof."
  rw [he.2]


-- NewTactic moved to BasicLean
OnlyTactic unfold rw sepcialize «let»
NewTheorem Mul.isIdentity MulEquiv.apply_symm_apply MulEquiv.map_mul
OnlyTheorem Mul.isIdentity MulEquiv.apply_symm_apply MulEquiv.map_mul
