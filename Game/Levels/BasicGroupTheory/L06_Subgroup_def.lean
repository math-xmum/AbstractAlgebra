import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 6

Introduction "A **subgroup** of a group $G$ is a nonempty subset $H$ that is closed under multiplication and inverses.

There is a useful one-condition criterion: $H$ is a subgroup of $G$ if and only if $H$ is nonempty and $a \\in H \\wedge b \\in H \\Rightarrow a \\cdot b^{-1} \\in H$.

In this level we prove this criterion. The proof uses `IsSubgroup.stepmk`, which lets us build a subgroup proof in steps, where each step can use the results of previous steps. We also use:
- `obtain ⟨x, hx⟩ := h` : destructures an existential hypothesis `h : \\exists x, P x`.
- `specialize h2 ha hbb` : applies arguments to a hypothesis in place.
- `assumption` : closes a goal that matches a hypothesis exactly.
"
open Monoid Group

variable {G :Type*} [Group G] {H: Set G}

/-- A predicate expressing that a set H is a subgroup of G:
  it contains 1, is closed under multiplication, and is closed under inverses. -/
structure IsSubgroup (H : Set G) : Prop where
  one_mem : 1 ∈ H
  mul_mem : ∀ {a b}, a ∈ H → b ∈ H → a * b ∈ H
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
(h3 : (1∈H)→ (∀ {a}, a∈ H → a⁻¹∈ H) → (∀ {a b}, a∈ H → b∈ H→ a * b∈H)) : IsSubgroup H :=
  ⟨h1, h3 h1 (h2 h1), h2 h1⟩

Statement (h1 : H.Nonempty) (h2 :∀ {a b:G}, (a∈H) → (b∈H) → ((a * b⁻¹)∈H)) : IsSubgroup H := by
  Hint "Apply the step-by-step subgroup constructor with `apply IsSubgroup.stepmk`. This creates three subgoals: (1) `1 ∈ H`, (2) closure under inverses (assuming 1 ∈ H), (3) closure under multiplication (assuming the previous two)."
  apply IsSubgroup.stepmk
  · Hint "We know `h1 : H.Nonempty`, which means `∃ x, x ∈ H`. Use `obtain ⟨x, hx⟩ := h1` to get a concrete `x` and `hx : x ∈ H`. (Type `⟨⟩` with `\\<` and `\\>`.)"
    obtain ⟨x,hx⟩ := h1
    Hint "Since `x ∈ H`, apply `h2` with `hx` twice: `have h := h2 hx hx` gives `x * x⁻¹ ∈ H`."
    have h := h2 hx hx
    Hint "The hypothesis `{h}` says `x * x⁻¹ ∈ H`. Use `group at {h}` to simplify `x * x⁻¹` to `1`."
    group at h
    Hint "Now `{h} : 1 ∈ H` matches the goal exactly. Use `exact {h}`."
    exact h
  · intro hone a ha
    Hint "We need `a⁻¹ ∈ H`. Since `1 ∈ H` and `a ∈ H`, use `have hbb := h2 hone ha` to get `1 * a⁻¹ ∈ H`."
    have hbb := h2 hone ha
    Hint "Simplify `1 * a⁻¹` to `a⁻¹` in `{hbb}` using `rw [one_mul] at {hbb}`."
    rw [one_mul] at hbb
    Hint "Now `{hbb}` matches the goal. Use `exact {hbb}` or `assumption`."
    assumption
  · Hint "Introduce all hypotheses with `intro hone hinv a b ha hb`."
    intro hone hinv a b ha hb
    Hint "First derive `b⁻¹ ∈ H` from closure under inverses: `have hbb := hinv hb`."
    have hbb:= hinv hb
    Hint "Now apply `h2` to `ha` and `hbb`. Use `specialize h2 {ha} {hbb}` to replace `h2` with the specialized result `a * b⁻¹⁻¹ ∈ H`."
    specialize h2 ha hbb
    Hint "Simplify `b⁻¹⁻¹` to `b` using `rw [inv_inv] at h2`. The theorem `inv_inv` states `(a⁻¹)⁻¹ = a`."
    rw [inv_inv] at h2
    assumption



NewTheorem IsSubgroup.stepmk Subgroup.mem_of_inv_mul_mem Subgroup.mem_of_mem_mul_inv Subgroup.inv_mem Subgroup.mul_mem inv_inv
