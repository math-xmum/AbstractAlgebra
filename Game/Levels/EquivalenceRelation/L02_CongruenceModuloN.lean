import Game.Metadata
import Mathlib.Algebra.Ring.Divisibility.Basic

World "EquivalenceRelation"
Level 2

Title "Congruence Modulo n"

Introduction "Two integers a and b are congruent modulo n if n divides (a - b). We write a = b (mod n). This is one of the most important equivalence relations in number theory. For example, 7 and 2 are congruent modulo 5, because 5 divides 7 - 2 = 5. We will prove that congruence modulo n is an equivalence relation."

Statement (preamble := constructor) (n : ℤ) : Equivalence (α := ℤ) (fun a b => n ∣ (a - b)) := by
  Hint "For reflexivity, we need to show n divides (x - x). Use `intro x` then simplify using `rw [sub_self]` and `exact dvd_zero n`."
  intro x
  rw [sub_self]
  exact dvd_zero n
  Hint "For symmetry, we need to show that if n divides (x - y), then n divides (y - x). Use `intro x y hxy`."
  intro x y hxy
  Hint "Note that y - x = -(x - y). We can use `have H : -(x - y) = y - x := neg_sub _ _` then rewrite."
  have H : -(x - y) = y - x := neg_sub _ _
  rw [← H]
  Hint "Now use `rw [dvd_neg]` to remove the negation, then `exact hxy`."
  rw [dvd_neg]
  exact hxy
  Hint "For transitivity, if n divides (x - y) and (y - z), then n divides (x - z). Use `intro x y z hxy hyz`."
  intro x y z hxy hyz
  Hint "The key identity is (x - y) + (y - z) = x - z. Use `have H : (x - y) + (y - z) = x - z := sub_add_sub_cancel _ _ _`."
  have H : (x - y) + (y - z) = x - z := sub_add_sub_cancel _ _ _
  rw [← H]
  Hint "Now use `exact dvd_add hxy hyz` since divisibility is closed under addition."
  exact dvd_add hxy hyz

Conclusion "Congruence modulo n is indeed an equivalence relation. This is the foundation of modular arithmetic."

NewTactic «have»
NewTheorem dvd_zero sub_self neg_sub dvd_neg dvd_add sub_add_sub_cancel
