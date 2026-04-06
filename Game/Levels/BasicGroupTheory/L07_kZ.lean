import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 7

Introduction "The integers $\\mathbb{Z}$ form a group under addition. For any integer $k$, the set $k\\mathbb{Z} = \\{k \\cdot n \\mid n \\in \\mathbb{Z}\\}$ is a subgroup of $\\mathbb{Z}$. For example, $2\\mathbb{Z}$ is the even integers.

In fact, every subgroup of $\\mathbb{Z}$ has the form $k\\mathbb{Z}$ for some $k \\in \\mathbb{N}$.

In this level, we show that the set $\\{a \\in \\mathbb{Z} \\mid a \\mod k = 0\\}$ forms an additive subgroup of $\\mathbb{Z}$, using `addsubgroupclass_make`. The key lemma is `Int.sub_emod`: `(a - b) % k = ((a % k) - (b % k)) % k`."

open Monoid

def subgroup_make {G : Type*} [Group G] (P : G → Prop) (h1 : P 1) (h2 :∀ {a b:G}, P a → P b → P (a * b⁻¹)): Subgroup G where
  carrier := {a | P a}
  mul_mem' := sorry
  one_mem' := h1
  inv_mem' := by
    simp only [Set.mem_setOf_eq]
    intro a ha
    have := (h2 h1 ha)
    simp only [one_mul] at this
    exact this

def addsubgroup_make {G : Type*} [AddGroup G] (P : G → Prop) (h1 : P 0) (h2 :∀ {a b:G}, P a → P b → P (a - b)): AddSubgroup G where
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
    intro ⟨⟩ ⟨⟩
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

def addsubgroupclass_make {G : Type*} [AddGroup G] (P : G → Prop) (h1 : P 0) (h2 :∀ {a b:G}, P a → P b → P (a - b)): AddSubgroupClass (SubSetP P) G where
  zero_mem := by
    intro s
    exact h1
  neg_mem := by
    intro s x
    simp only [SubSetP.def]
    apply neg_mem P h1 h2
  add_mem := by
    intro s a b
    simp only [SubSetP.def]
    intro ha hb
    have hnb := neg_mem P h1 h2 b hb
    have := h2 ha hnb
    simp only [sub_neg_eq_add] at this
    exact this


#check Int.sub_emod

variable (k : ℤ) in
Statement : AddSubgroupClass (SubSetP (· %k = 0)) ℤ :=
  by
    apply addsubgroupclass_make
    · simp only [Int.zero_emod]
    Hint "Introduce the elements and hypotheses with `intro a b` followed by `intro ha hb`."
    intro a b
    intro ha hb
    Hint "Rewrite using `rw [Int.sub_emod]` to express `(a - b) % k` in terms of `a % k` and `b % k`."
    rw [Int.sub_emod]
    Hint "Now `ha : a % k = 0` and `hb : b % k = 0`. Use `simp [ha, hb]` to substitute these and simplify."
    simp only [ha, hb, sub_self, Int.zero_emod]


NewTheorem SubSetP.def Int.sub_emod addsubgroupclass_make
