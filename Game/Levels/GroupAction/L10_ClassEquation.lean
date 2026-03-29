import Game.Metadata
import Mathlib.GroupTheory.PGroup

World "GroupAction"

Level 10

Title "The Class Equation"

Introduction "
The **class equation** is obtained by applying the orbit-counting
formula to the conjugation action of G on itself:
  |G| = |Z(G)| + Σ [G : C_G(gᵢ)]
where the sum runs over representatives gᵢ of non-central conjugacy classes,
and C_G(gᵢ) is the centralizer of gᵢ.

A key consequence: for a **p-group** G (a group whose order is a power of p),
the class equation gives |Z(G)| ≡ |G| ≡ 0 (mod p). Since the identity
is always in Z(G), we conclude |Z(G)| ≥ p > 1.

Therefore the center of a nontrivial p-group is always nontrivial.

In Mathlib, a p-group is `IsPGroup p G`, meaning every element has order
a power of p. The center is `Subgroup.center G`.

The key tool is the **fixed point theorem** for p-groups:
if a p-group acts on a finite set, the number of fixed points is
congruent to the cardinality of the set modulo p
(`IsPGroup.card_modEq_card_fixedPoints`).

Applied to the conjugation action, the fixed points are exactly Z(G).
"

open MulAction

variable {p : ℕ} {G : Type*} [Group G] [Fact (Nat.Prime p)]

Statement (hG : IsPGroup p G) [Finite G] [Nontrivial G] :
    Nontrivial (Subgroup.center G) := by
  Hint "This follows from the class equation. The key fact is that
  `IsPGroup.center_nontrivial` packages the entire argument:
  the conjugation action's fixed points are Z(G), and the fixed-point
  theorem forces |Z(G)| ≡ |G| ≡ 0 (mod p), so |Z(G)| ≥ p > 1.
  Use `exact hG.center_nontrivial`."
  exact hG.center_nontrivial

Conclusion "
The center of every nontrivial p-group is nontrivial.
This seemingly simple fact has profound consequences:
- It is the base case for proving that p-groups are **nilpotent**
  (by induction on |G|, quotienting by Z(G)).
- It is used in the proof of the **Sylow theorems**.
- It implies that every group of order p² is abelian.

In Mathlib, this is `IsPGroup.center_nontrivial`, which internally
uses the fixed-point theorem `IsPGroup.card_modEq_card_fixedPoints`
applied to the conjugation action via `ConjAct`.
"

NewTheorem IsPGroup.center_nontrivial IsPGroup.card_modEq_card_fixedPoints ConjAct.fixedPoints_eq_center Subgroup.center IsPGroup
