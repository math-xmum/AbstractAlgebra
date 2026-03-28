import Game.Metadata

World "BasicGroupTheory"

Level 6

Introduction "
A subgroup of a group $G$ is a nonempty subset $H$ of $G$ such that $*$ is closed under $H$ and inverse.

We have a criterion for a set H to be a subgroup of $G$:
If H is non-empty and a ∈  H ∧ b ∈  H implies a * b⁻¹ ∈ H
then H is a subgroup of G

The follow theorem this criterion.
"
open Monoid Group

variable {G :Type*} [Group G] {H: Set G}

/-- A predicate for a set to be a subgroup: it must be closed under multiplication
and contain inverses. -/
structure IsSubgroup (H : Set G) : Prop where
  mul_mem_and_one_mem : 1 ∈ H ∧ ∀ {a b}, a ∈ H → b ∈ H → a * b ∈ H
  inv_mem : ∀ {a}, a ∈ H → a⁻¹ ∈ H

lemma And.intro' (h1 : P) (h2 : P→Q) : P ∧ Q := ⟨h1, h2 h1⟩

/--
Suppose you want to proof proposition R using `mk'.
So one have to prove proposition P and Q respectively.
This magical lemma allows one assume P holds when proving Q.
-/
def mk.intro {h1 : P} {h2 : P→Q} (mk : P → Q → R) : R := mk h1 (h2 h1)

/--
Instead of proving H satisfies the conditions to be a subgroup of G separately, this lemma allows one prove the conditions step by step such that using the result already proved before.
-/
lemma IsSubgroup.stepmk (h1 : 1 ∈H) (h2 : (1∈H)→(∀ {a}, a∈H →  a⁻¹∈ H))
(h3 : (1∈H)→ (∀ {a}, a∈ H → a⁻¹∈ H) → (∀ {a b}, a∈ H → b∈ H→ a * b∈H)) : IsSubgroup H:= by
  constructor
  · exact ⟨h1, h3 h1  (h2 h1)⟩
  exact h2 h1

Statement (h1 : H.Nonempty) (h2 :∀ {a b:G}, (a∈H) → (b∈H) → ((a * b⁻¹)∈H)) : IsSubgroup H := by
  Hint "Unfold the definition using `IsSubgroup.stepmk'."
  apply IsSubgroup.stepmk
  · Hint "Note that `H.Nonempty = ∃ x , x ∈ H'. One can use obtain ⟨x,hx⟩ := h1 to use the existance statement h1. Here `⟨' and `⟩' can be typed by `\\<' and `\\>' respectively.  "
    obtain ⟨x,hx⟩ := h1
    Hint "Use `h2' "
    have h := h2 hx hx
    Hint "Apply `group' at {h}"
    group at h
    Hint "Not it is exactly the statement {h}. "
    exact h
  · intro hone a ha
    Hint "Prove `a⁻¹∈ H' using `h2' "
    have hbb := h2 hone ha
    Hint "simp at {hbb}"
    simp at hbb
    Hint "Except using `exact {hbb}' one also can use `assumption' to finish the goal.  "
    assumption
  · Hint "Intro all the hypothesis by `intro hone hinv a b ha hb'  "
    intro hone hinv a b ha hb
    Hint "Show that b⁻¹ ∈ H"
    have hbb:= hinv hb
    Hint "Use {hbb} and {h2}"
    Hint " Instead of using `have' one also can use
    `specialize {h2} {ha} {hbb}' to replace {h2} "
    specialize h2 ha hbb
    Hint "Clean up the expression at {h2} by `simp'"
    simp at h2
    assumption



NewTheorem IsSubgroup.stepmk Subgroup.mem_of_inv_mul_mem Subgroup.mem_of_mem_mul_inv Subgroup.inv_mem Subgroup.mul_mem
