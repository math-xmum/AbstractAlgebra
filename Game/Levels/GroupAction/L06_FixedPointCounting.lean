import Game.Metadata
import Mathlib.GroupTheory.PGroup

World "GroupAction"

Level 6

Title "Fixed Point Counting for p-Groups"

Introduction "
This is the most important theorem in this world.

If G is a p-group (a group whose order is a power of p) acting on a finite set X, then
|X| ≡ |Xᴳ| (mod p), where Xᴳ = {x ∈ X | g·x = x for all g ∈ G} is the set of fixed points.

The proof partitions X into orbits. Each orbit has size dividing |G|, hence a power of p.
Non-trivial orbits (size > 1) have size divisible by p, so they vanish mod p.
What remains is the set of fixed points (orbits of size 1).

This single result drives all three Sylow theorems and many other applications.

In Lean, this is `IsPGroup.card_modEq_card_fixedPoints`.
"

open MulAction

variable {p : ℕ} {G : Type*} [Group G] {α : Type*} [MulAction G α]

Statement [Fact (Nat.Prime p)] (hG : IsPGroup p G) [Finite α] [Finite G] :
    Nat.card α ≡ Nat.card (MulAction.fixedPoints G α) [MOD p] := by
  Hint "Apply the mathlib theorem `IsPGroup.card_modEq_card_fixedPoints` directly."
  exact hG.card_modEq_card_fixedPoints α

Conclusion "
The fixed-point counting lemma is the workhorse of p-group theory.

Key applications:
1. **Class equation**: Taking X = G with conjugation action gives
   |G| ≡ |Z(G)| (mod p), so p-groups have non-trivial centers.
2. **Sylow existence**: A p-group acting on a set of subgroups
   produces fixed points that become Sylow subgroups.
3. **Sylow conjugacy and counting**: The number of Sylow p-subgroups
   satisfies nₚ ≡ 1 (mod p).
"

NewTheorem IsPGroup.card_modEq_card_fixedPoints IsPGroup MulAction.fixedPoints
