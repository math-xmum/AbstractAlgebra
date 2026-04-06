import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 10

Introduction "A group where every element is its own inverse ($a^2 = 1$ for all $a$) is called an **elementary abelian 2-group**. In this level, we prove that such a group is abelian: $a \\cdot b = b \\cdot a$ for all $a, b$.

The key insight is: if $a \\cdot a = 1$, then $a^{-1} = a$. Once we establish this, we compute $(a \\cdot b)^{-1} = b^{-1} \\cdot a^{-1} = b \\cdot a$, so $a \\cdot b = b \\cdot a$.

New tactics:
- `have name : type := proof` : introduces a local lemma.
- `nth_rw n [h]` : rewrites only the $n$-th occurrence of the pattern matching `h`."

open Monoid Group

variable {G : Type*} [Group G]

/-
If $G$ is a group such that $a^2 = 1$ for all $a in G$, then $G$ is abelian.
"
-/

Statement  (H: ∀ a : G, a * a = 1) : ∀ a b :G, a*b=b*a := by
  Hint "First prove the helper lemma `a⁻¹ = a` for all `a`. Use `have inv_eq_self : ∀ a : G, a⁻¹ = a := by ...` to state and prove it inline."
  have inv_eq_self : ∀ a : G, a⁻¹ = a := by
    Hint "Use `intro a` to introduce the universally quantified variable."
    intro a
    Hint "The theorem `mul_eq_one_iff_inv_eq` states `a * b = 1 ↔ a⁻¹ = b`. Rewrite the goal with `rw [<-mul_eq_one_iff_inv_eq]` to reduce it to `a * a = 1`, which is exactly `H a`."
    rw [<-mul_eq_one_iff_inv_eq]
    exact (H a)
  intro a b
  Hint "Now prove `a * b = b * a`. The idea: rewrite `a * b` as `(a * b)⁻¹` (since every element equals its inverse), then expand to `b⁻¹ * a⁻¹`, and rewrite back. Use `rw [<-inv_eq_self (a * b)]` first. Then use `nth_rw 1 [<-inv_eq_self a]` and `nth_rw 1 [<-inv_eq_self b]` to selectively rewrite specific occurrences."
  rw [<-inv_eq_self (a * b)]
  nth_rw 1 [<-inv_eq_self a]
  nth_rw 1 [<-inv_eq_self b]
  Hint "Use `group` to simplify `(a * b)⁻¹ = b⁻¹ * a⁻¹` and close the goal."
  group


#check mul_eq_one_iff_eq_inv

NewTheorem mul_eq_one_iff_inv_eq mul_eq_one_iff_eq_inv add_eq_zero_iff_neg_eq  add_eq_zero_iff_eq_neg
