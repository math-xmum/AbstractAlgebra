import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 3


variable {S :Type*}



Introduction "
**Congruence modulo $n$** is a fundamental equivalence relation on the integers. We say $a \\equiv b \\pmod{n}$ when $n \\mid (a - b)$.

In Lean, divisibility `n ∣ k` means there exists some integer `m` with `k = n * m`.

We must verify the three equivalence-relation properties:
- **Reflexivity**: $n \\mid (x - x) = n \\mid 0$, which always holds.
- **Symmetry**: If $n \\mid (x - y)$, then $n \\mid -(x-y) = n \\mid (y - x)$.
- **Transitivity**: If $n \\mid (x - y)$ and $n \\mid (y - z)$, then $n \\mid ((x-y)+(y-z)) = n \\mid (x - z)$.

This proof uses the `have` tactic, which introduces a new intermediate fact into the context. The syntax is `have H : <type> := <proof_term>`. This is useful when you need to establish a stepping-stone result before applying it.
"

Statement (preamble := constructor ) (n : ℤ): Equivalence (α := ℤ) (fun a b => n ∣ (a - b)) := by
  Hint "**Reflexivity.** The goal asks to show `n ∣ (x - x)` for any `x`. Start with `intro x` to pick an arbitrary integer."
  intro x
  Hint "Now rewrite `x - x` to `0` using `rw [sub_self]`. The lemma `sub_self` states `∀ a, a - a = 0`."
  rw [sub_self]
  Hint "The goal is `n ∣ 0`. Use `exact dvd_zero n`, which is the lemma stating every integer divides zero."
  exact dvd_zero n
  Hint "**Symmetry.** Introduce `x`, `y`, and the hypothesis `hxy : n ∣ (x - y)` with `intro x y hxy`."
  intro x y hxy
  Hint "We need `n ∣ (y - x)`. The key identity is `-(x - y) = y - x`. Use `have H : -(x - y) = y - x := neg_sub _ _` to record this fact.

The `have` tactic introduces a new named hypothesis into the context without changing the goal."
  have H : - (x - y) = y-x := neg_sub _ _
  Hint "Rewrite the goal using {H} backwards: `rw [←{H}]` turns `n ∣ (y - x)` into `n ∣ -(x - y)`.

The `←` (typed as `\\left` or `\\l`) makes `rw` apply the equation right-to-left."
  rw [<-H]
  Hint "Now use `rw [dvd_neg]` to simplify `n ∣ -(x - y)` to `n ∣ (x - y)`. The lemma `dvd_neg` states `n ∣ -k ↔ n ∣ k`."
  rw [dvd_neg]
  Hint "The goal is now exactly {hxy}. Use `exact {hxy}`."
  exact hxy
  Hint "**Transitivity.** Introduce `x`, `y`, `z`, and hypotheses `hxy : n ∣ (x - y)` and `hyz : n ∣ (y - z)` with `intro x y z hxy hyz`."
  intro x y z hxy hyz
  Hint "The algebraic trick: $(x - y) + (y - z) = x - z$. Record it with `have H : (x - y) + (y - z) = x - z := sub_add_sub_cancel _ _ _`."
  have H : (x - y) + (y - z) = x - z := sub_add_sub_cancel _ _ _
  Hint "Rewrite backwards with `rw [←{H}]` to turn the goal into `n ∣ (x - y) + (y - z)`."
  rw [<-H]
  Hint "If `n` divides two numbers, it divides their sum. Use `exact dvd_add {hxy} {hyz}`, applying the lemma `dvd_add`."
  exact dvd_add hxy hyz


-- NewTactic moved to BasicLean
OnlyTactic intro rfl rw exact simp «have»
