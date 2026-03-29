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

private lemma one_mem_of_nonempty (h1 : H.Nonempty) (h2 : ∀ {a b : G}, a ∈ H → b ∈ H → a * b⁻¹ ∈ H) :
    1 ∈ H := by
  obtain ⟨x, hx⟩ := h1
  have h := h2 hx hx
  group at h
  exact h

private lemma inv_mem_of_criterion (h2 : ∀ {a b : G}, a ∈ H → b ∈ H → a * b⁻¹ ∈ H)
    (hone : 1 ∈ H) (ha : a ∈ H) : a⁻¹ ∈ H := by
  have hbb := h2 hone ha; simp at hbb; exact hbb

private lemma mul_mem_of_criterion (h2 : ∀ {a b : G}, a ∈ H → b ∈ H → a * b⁻¹ ∈ H)
    (hinv : ∀ {a}, a ∈ H → a⁻¹ ∈ H) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  specialize h2 ha (hinv hb); simp at h2; exact h2

Statement (h1 : H.Nonempty) (h2 :∀ {a b:G}, (a∈H) → (b∈H) → ((a * b⁻¹)∈H)) : IsSubgroup H := by
  Hint "Unfold the definition using `IsSubgroup.stepmk'."
  apply IsSubgroup.stepmk
  · Hint "Note that `H.Nonempty = ∃ x , x ∈ H'. One can use obtain ⟨x,hx⟩ := h1 to use the existance statement h1. Here `⟨' and `⟩' can be typed by `\\<' and `\\>' respectively.  "
    Hint "Use `h2' "
    exact one_mem_of_nonempty h1 h2
  · intro hone a ha
    Hint "Prove `a⁻¹∈ H' using `h2' "
    exact inv_mem_of_criterion h2 hone ha
  · Hint "Intro all the hypothesis by `intro hone hinv a b ha hb'  "
    intro hone hinv a b ha hb
    Hint "Show that b⁻¹ ∈ H"
    exact mul_mem_of_criterion h2 hinv ha hb



NewTheorem IsSubgroup.stepmk Subgroup.mem_of_inv_mul_mem Subgroup.mem_of_mem_mul_inv Subgroup.inv_mem Subgroup.mul_mem
