import Game.Metadata
-- import Mathlib

World "GroupBasics"

Level 10

Introduction "
If G is a group such that a * a = 1 for all a in G, then G is abelian.
"

open Monoid Group

variable {G : Type*} [Group G]

/-
If $G$ is a group such that $a^2 = 1$ for all $a in G$, then $G$ is abelian.
"
-/

Statement  (H: ∀ a : G, a * a = 1) : ∀ a b :G, a*b=b*a := by
  Hint "We first prove the claim that `a⁻¹ = a` for all a.
  State the claim by `have inv_eq_self : ∀ a : G, a⁻¹ = a`.
  "
  have inv_eq_self : ∀ a : G, a⁻¹ = a := by
    Hint "Use `intro a` to reveal the goal"
    intro a
    Hint "Note that `mul_eq_one_iff_inv_eq` stats that  a*b = 1 ↔ a⁻¹ = b. Use this to rewrite the goal and then finish the proof.
    BTW: You also can use `mul_eq_one_iff_eq_inv`. "
    rw [<-mul_eq_one_iff_inv_eq]
    exact (H a)
  intro a b
  Hint "Use {inv_eq_self} smartly"
  Hint "You can use `nth_rw' to specify the location of the term to rewrite"
  rw [<-inv_eq_self (a * b)]
  nth_rw 1 [<-inv_eq_self a]
  nth_rw 1 [<-inv_eq_self b]
  Hint "Use `group' to finish the proof"
  group


#check mul_eq_one_iff_eq_inv

NewTheorem mul_eq_one_iff_inv_eq mul_eq_one_iff_eq_inv add_eq_zero_iff_neg_eq  add_eq_zero_iff_eq_neg
