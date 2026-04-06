import Mathlib.Tactic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Coset.Basic

/-!
# MAT205 Lecture 01: Review of Basics — Exercises

These exercises accompany Lecture 1 (Review of Basics).
Students should attempt each `sorry` and replace it with a proof.
-/

section GroupBasics

variable {G : Type*} [Group G]

/-!
## Exercise 1: Identity is unique

If `e'` is also an identity element (i.e., `e' * a = a` for all `a`),
then `e' = 1`.
-/
theorem identity_unique (e' : G) (h : ∀ a : G, e' * a = a) : e' = 1 := by
  sorry

/-!
## Exercise 2: Inverse is unique

If `b * a = 1`, then `b = a⁻¹`.
-/
theorem inverse_unique (a b : G) (h : b * a = 1) : b = a⁻¹ := by
  sorry

/-!
## Exercise 3: Cancellation law

From `a * b = a * c`, deduce `b = c`.
Hint: Multiply both sides by `a⁻¹` on the left.
-/
theorem left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  sorry

/-!
## Exercise 4: Inverse of product

Prove that `(a * b)⁻¹ = b⁻¹ * a⁻¹`.
Hint: Show that `b⁻¹ * a⁻¹` is the inverse of `a * b` by checking the defining property.
-/
theorem inv_mul_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

end GroupBasics


section Homomorphisms

variable {G H : Type*} [Group G] [Group H]

/-!
## Exercise 5: Homomorphism maps identity to identity

If `f : G →* H` is a group homomorphism, then `f 1 = 1`.

Note: This is already `map_one`, but prove it from scratch using only `map_mul`.
-/
theorem hom_map_one (f : G →* H) : f 1 = 1 := by
  have h : f (1 * 1) = f 1 * f 1 := f.map_mul 1 1
  rw [one_mul] at h
  sorry

/-!
## Exercise 6: Homomorphism maps inverse to inverse

If `f : G →* H`, then `f a⁻¹ = (f a)⁻¹`.
Hint: Show `f a * f a⁻¹ = 1`.
-/
theorem hom_map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  sorry

/-!
## Exercise 7: Composition of homomorphisms

The composition of two group homomorphisms is a homomorphism.
-/
theorem hom_comp_map_mul {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (a b : G) : g (f (a * b)) = g (f a) * g (f b) := by
  sorry

end Homomorphisms


section Subgroups

variable {G : Type*} [Group G]

/-!
## Exercise 8: Center is a subgroup

The center `Z(G) = {g ∈ G | ∀ x, g * x = x * g}` is a subgroup.
Hint: Check closure under multiplication and inverse.
-/
theorem center_mul_mem (a b : G) (ha : ∀ x : G, a * x = x * a)
    (hb : ∀ x : G, b * x = x * b) : ∀ x : G, a * b * x = x * (a * b) := by
  sorry

/-!
## Exercise 9: Abelian implies all subgroups normal

If `G` is abelian (i.e., `CommGroup G`), then every subgroup is normal.
-/
theorem abelian_subgroup_normal {G : Type*} [CommGroup G] (H : Subgroup G) :
    H.Normal := by
  sorry

end Subgroups


section Cosets

variable {G : Type*} [Group G] (H : Subgroup G)

/-!
## Exercise 10: Self in own coset

For any `g : G`, we have `g ∈ g • (H : Set G)`.
Hint: Use `1 ∈ H` and `g * 1 = g`.
-/
theorem mem_own_coset (g : G) : ∃ h ∈ H, g * h = g := by
  exact ⟨1, H.one_mem, mul_one g⟩

end Cosets
