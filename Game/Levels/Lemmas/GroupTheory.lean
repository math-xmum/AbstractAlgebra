import Mathlib.Tactic.Group
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Coset

section Subgroup
variable {G : Type*} [Group G] {H : Subgroup G} {a b g: G}
open scoped Pointwise
open Pointwise

/--
If `H` is a subgroup of `G`, `a ∈ H` and `b ∈ H`, then `a⁻¹ * b ∈ H`.
-/
lemma Subgroup.mem_of_inv_mul_mem  (ha : a ∈ H) (hb : b ∈ H) : a⁻¹ * b ∈ H := by
  replace ha : a⁻¹ ∈ H := Subgroup.inv_mem _ ha
  exact Subgroup.mul_mem _ ha hb


/--
If `H` is a subgroup of `G`, `a ∈ H` and `b ∈ H`, then `a * b⁻¹ ∈ H`.
-/
lemma Subgroup.mem_of_mem_mul_inv (ha : a ∈ H) (hb : b ∈ H) :  a * b⁻¹ ∈ H := by
  replace hb : b⁻¹ ∈ H := Subgroup.inv_mem _ hb
  exact Subgroup.mul_mem _ ha hb

/--
For any x ∈ g • H, we have  y ∈ g • H ↔ x⁻¹ * y ∈ H.
-/
lemma Subgroup.mem_coset_iff_diff_mem_subgroup (hx : x ∈ g • (H : Set G)) :  y ∈  g • (H : Set G) ↔  x⁻¹ * y ∈ H := by
  constructor
  · intro hy
    replace hx :=(mem_leftCoset_iff _).1 hx
    replace hy :=(mem_leftCoset_iff _).1 hy
    have hxy :x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group
    rw [hxy]
    apply Subgroup.mem_of_inv_mul_mem hx hy
  · intro hxy
    have hgx : g⁻¹ * x ∈ H := (mem_leftCoset_iff _).1 hx
    use ((g⁻¹*x) * (x⁻¹ *y))
    constructor
    · exact Subgroup.mul_mem _ hgx hxy
    simp; group


end Subgroup

section MonoidSet

namespace Set

variable {G : Type*} [Monoid G] {H : Set G} {a b g: G}
/--
If `G` is a monoid, then `Set G` is a monoid under the multiplication defined by

S * T := { x*y | x∈S, y∈T}

Similar monoid struction is defined on `Finset G`.

-/


instance Monoid.instHMulSet : HMul (Set G) (Set G) (Set G)where
  hMul:= fun S T => (fun x =>  x.1 * x.2) '' ( S ×ˢ T)

@[simp]
lemma mul_set_def (S T : Set G) : S * T = (fun x =>  x.1 * x.2) '' ( S ×ˢ T) := rfl

/--
Suppose S and T are two subset of G, then x in S * T ↔ ∃ (a b:G), (a ∈ S ∧ b ∈ T ∧  a*b=x).
-/
lemma mem_mul_set_iff {S T : Set G}: x ∈  S * T ↔ ∃ (a b:G), (a ∈ S ∧ b ∈ T ∧  a*b=x):= by
  constructor
  · simp_rw [mul_set_def,Set.mem_image, Set.mem_prod, Prod.exists, exists_and_left, forall_exists_index,
    and_imp]
    intro a b ha hb hab
    exact ⟨a, ha,⟨b,hb,hab⟩⟩
  · intro h
    obtain ⟨a,b,ha,hb,hab⟩ := h
    simp_rw [mul_set_def,Set.mem_image, Set.mem_prod, Prod.exists]
    use a,b



instance Monoid.instSet: Monoid (Set G) where
  mul := fun S T => S * T
  one := ({1} : Set G)
  mul_assoc := by
    intro S T U
    ext
    constructor
    . intro H
      rw [mem_mul_set_iff] at H
      obtain ⟨ab,c,hab,hc,habc⟩ := H
      rw [mem_mul_set_iff] at hab
      obtain ⟨a,b,ha,hb,hab⟩ := hab
      rw [mem_mul_set_iff]
      use a, (b*c)
      refine ⟨ha,?_,by rw [<-habc,<-hab];group⟩
      rw [mem_mul_set_iff]
      refine ⟨b,c,hb,hc,rfl⟩
    . intro H
      rw [mem_mul_set_iff] at H
      obtain ⟨a,bc,ha,hbc,habc⟩ := H
      rw [mem_mul_set_iff] at hbc
      obtain ⟨b,c,hb,hc,hbc⟩ := hbc
      rw [mem_mul_set_iff]
      use (a*b), c
      refine ⟨?_,hc,by rw [<-habc,<-hbc];group⟩
      rw [mem_mul_set_iff]
      refine ⟨a,b,ha,hb,rfl⟩
  one_mul := by
    intro S
    ext; rw [mem_mul_set_iff]
    constructor
    · intro H
      obtain ⟨a,b,ha,hb,hab⟩ := H
      have ha : a = 1:= Set.mem_singleton_iff.2 ha
      rw [ha,one_mul] at hab
      rw [<-hab]
      exact hb
    · intro H
      refine ⟨1,x,Set.mem_singleton_iff.1 rfl,H,one_mul x⟩
  mul_one := by
    intro S
    ext; rw [mem_mul_set_iff]
    constructor
    · intro H
      obtain ⟨a,b,ha,hb,hab⟩ := H
      have hb : b = 1:= Set.mem_singleton_iff.2 hb
      rw [hb,mul_one] at hab
      rw [<-hab]
      exact ha
    · intro H
      refine ⟨x,1,H,Set.mem_singleton_iff.1 rfl,mul_one x⟩


end Set

end MonoidSet


section GroupHom

variable {G H: Type*} [Group G] [Group H] (f: G → H) (hf : ∀ x y :G, f (x * y) = f x * f y )

abbrev GroupHom.intro  : G →* H where
  toFun := f
  map_mul' := hf
  map_one' := by
    have h1 : 1 * 1 = 1 := mul_one (1:G)
    apply_fun f at h1
    rw [hf] at h1
    nth_rw 3 [<-mul_one (f 1)] at h1
    exact mul_left_cancel h1

@[simp]
lemma GroupHom.coe_fun_eq : GroupHom.intro f hf = f := rfl

section MulEquiv_intro
variable {G H : Type*} [Monoid G] [Monoid H] (toFun : G →H) (invFun : H → G) (left_inv : Function.LeftInverse invFun toFun)
(right_inv: Function.RightInverse invFun toFun) (toFun_mul : ∀ x y, toFun (x * y) = toFun x * toFun y)

abbrev MulEquiv.intro  : G ≃* H where
  toFun := toFun
  invFun := invFun
  left_inv := left_inv
  right_inv := right_inv
  map_mul' := toFun_mul

@[simp]
lemma MulEquiv.intro_toFun_apply : MulEquiv.intro toFun invFun left_inv right_inv toFun_mul (x:G) = toFun x := rfl

@[simp]
lemma MulEquiv.intro_invFun_apply : (MulEquiv.intro toFun invFun left_inv right_inv toFun_mul).symm (x:H) = invFun x := rfl


end MulEquiv_intro


/--
The composition of three functions is associative.
-/
lemma Function.comp_assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl


end GroupHom
