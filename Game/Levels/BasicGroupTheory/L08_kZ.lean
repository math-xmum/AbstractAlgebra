import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 8

Introduction "
For example, ℤ is a group under addition.
Now the set of even integers, 2ℤ := {2n | n ∈ ℤ }, is a subgroup of ℤ.
More generally, kℤ := {k*n | n ∈ ℤ } is also a subgroup of ℤ.
Morover, all subgoup of ℤ is of the form kℤ for some k ∈ ℕ.

In fact, ℕ → {subgroup of ℤ} given by k ↦ kℤ is a bijection.
"

open Monoid

lemma subgroup_make {G : Type*} [Group G] (P : G → Prop) (h1 : P 1) (h2 :∀ {a b:G}, P a → P b → P (a * b⁻¹)): Subgroup G where
  carrier := {a | P a}
  mul_mem' := sorry
  one_mem' := h1
  inv_mem' := by
    simp only [Set.mem_setOf_eq]
    intro a ha
    have := (h2 h1 ha)
    simp only [one_mul] at this
    exact this

lemma addsubgroup_make {G : Type*} [AddGroup G] (P : G → Prop) (h1 : P 0) (h2 :∀ {a b:G}, P a → P b → P (a - b)): AddSubgroup G where
  carrier := {a | P a}
  add_mem' := sorry
  zero_mem' := h1
  neg_mem' := by
    simp only [Set.mem_setOf_eq]
    intro a ha
    have := (h2 h1 ha)
    simp only [zero_sub] at this
    exact this

inductive SubSetP  (P : G → Prop)
 | carrier


instance (P : α → Prop): SetLike (SubSetP P) α where
  coe := fun _ => {a  | P a}
  coe_injective' := by
    intro _ _
    simp

/--
 For a prediction P, SubSetP defines the subset {a : α | P a} of α
-/
lemma SubSetP.def {s : SubSetP P} : a ∈ s ↔ P a := by rfl

--LemmaDoc SubSetP.def as "SubSetP.def" in  "SubSet" "For a prediction P, SubSetP defines the subset {a : α | P a} of α"

lemma neg_mem {G : Type*} [AddGroup G] (P : G → Prop) (h1 : P 0) (h2 :∀ {a b:G}, P a → P b → P (a - b)): ∀ a : G, P a → P (-a) := by
    intro x hx
    have := (h2 h1 hx)
    simp only [zero_sub] at this
    exact this

lemma addsubgroupclass_make {G : Type*} [AddGroup G] (P : G → Prop) (h1 : P 0) (h2 :∀ {a b:G}, P a → P b → P (a - b)): AddSubgroupClass (SubSetP P) G where
  zero_mem := by
    intro s
    exact h1
  neg_mem := by
    intro s x
    simp [SubSetP.def]
    apply neg_mem P h1 h2
  add_mem := by
    intro s a b
    simp [SubSetP.def]
    intro ha hb
    have hnb := neg_mem P h1 h2 b hb
    have := h2 ha hnb
    simp only [sub_neg_eq_add] at this
    exact this


#check Int.sub_emod

Statement : AddSubgroupClass (SubSetP (· %k = 0)) ℤ :=
  by
    apply addsubgroupclass_make
    · simp
    Hint "Intro all elements"
    intro a b
    intro ha hb
    Hint "Use Int.sub_emod"
    rw [Int.sub_emod]
    Hint "Use hypothesis to simp the goal"
    simp [ha,hb]


NewTheorem SubSetP.def Int.sub_emod addsubgroupclass_make
