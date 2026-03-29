import Game.Metadata
import Mathlib.Algebra.Group.Subgroup.Basic

World "GroupAction"

Level 8

Title "The Normalizer"

Introduction "
The normalizer N_G(H) of a subgroup H is defined as
  N_G(H) = {g ∈ G | gHg⁻¹ = H}.
It is the largest subgroup of G in which H is normal.

In Mathlib, the normalizer of a subgroup H is `H.normalizer`, and
membership is characterized by `Subgroup.mem_normalizer_iff`:
  g ∈ H.normalizer ↔ ∀ h, h ∈ H ↔ g * h * g⁻¹ ∈ H.

Your goal: show that H is contained in its own normalizer, i.e., H ≤ N_G(H).
This is intuitively clear: if g ∈ H, then gHg⁻¹ = H by closure of H
under multiplication and inverses.
"

variable {G : Type*} [Group G] (H : Subgroup G)

/-- Every element of H normalizes H. -/
private lemma le_normalizer_aux (x : G) (hx : x ∈ H) :
    x ∈ H.normalizer := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx)
  · intro hh
    have : x⁻¹ * (x * h * x⁻¹) * x = h := by group
    rw [← this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hx) hh) hx

Statement : H ≤ H.normalizer := by
  Hint "We need to show every element of H is in the normalizer of H.
  Start with `intro x hx` to take an arbitrary element x ∈ H."
  intro x hx
  Hint "Now we must show x ∈ H.normalizer. Use `rw [Subgroup.mem_normalizer_iff]` to
  unfold the definition of the normalizer."
  rw [Subgroup.mem_normalizer_iff]
  Hint "We need to show: for all h, h ∈ H ↔ x * h * x⁻¹ ∈ H.
  Introduce h with `intro h` and then split using `constructor`."
  intro h
  constructor
  · Hint "If h ∈ H and x ∈ H, then x * h * x⁻¹ ∈ H by closure.
    Use `exact H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx)`."
    intro hh
    exact H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx)
  · Hint "For the reverse direction, we need to show that if x * h * x⁻¹ ∈ H
    then h ∈ H. Since x⁻¹ ∈ H, we can conjugate back.
    Use the fact that h = x⁻¹ * (x * h * x⁻¹) * x."
    intro hh
    have key : x⁻¹ * (x * h * x⁻¹) * x = h := by group
    rw [← key]
    exact H.mul_mem (H.mul_mem (H.inv_mem hx) hh) hx

Conclusion "
Well done! You have shown that every subgroup is contained in its own normalizer.
In Mathlib, this is `Subgroup.le_normalizer`. This fact is the starting point
for studying normality: H is normal in G precisely when H.normalizer = ⊤.
"

NewTheorem Subgroup.mem_normalizer_iff Subgroup.normalizer Subgroup.le_normalizer Subgroup.mul_mem Subgroup.inv_mem
