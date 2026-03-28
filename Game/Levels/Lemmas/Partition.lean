import Mathlib.Data.Set.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.SetNotation


/-- A collection `c : Set (Set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def IsPartition (c : Set (Set α)) := ∅ ∉ c ∧ ∀ a, ∃! b, b ∈ c ∧ a ∈ b

def IsPartition' (c : Set (Set α)) := ∅ ∉ c ∧ ( ⋃₀ c = Set.univ) ∧ ( ∀ a ∈ c,  ∀ b ∈ c, a ∩ b ≠ ∅ → a = b)

#print IsPartition'


namespace Setoid

variable {α :Type*} [inst: Setoid α] {x : α}

-- abbrev equivclass (x : α):  Set α := {y | x ≈ y}

lemma mem_selfequivclass (x : α) : x ∈ {y | x ≈ y} := by
   rewrite [Set.mem_setOf_eq]
   exact Setoid.refl _

lemma mem_equivclass_iff_equiv (x : α): y ∈ {y | x ≈ y} ↔  x ≈ y := by
  rewrite [Set.mem_setOf_eq]
  rfl


lemma equivclass_eq_iff_equiv  {x y: α}: {z | x ≈ z} = {z | y ≈ z}  ↔ x ≈ y := by
  constructor <;> intro H
  have hy := Setoid.mem_selfequivclass y
  rw [<-H] at hy
  rw [Setoid.mem_equivclass_iff_equiv] at hy
  exact hy
  ext z
  repeat rw [Setoid.mem_equivclass_iff_equiv]
  constructor
  intro H1
  exact Setoid.trans (Setoid.symm H) H1
  intro H1
  exact Setoid.trans H H1

lemma equivclass_nonempty (x : α) : {y | x ≈ y} ≠ ∅ := by
  intro h
  have : x ∈ ({y | x ≈ y} : Set α) := Setoid.refl x
  rw [h] at this
  exact (Set.mem_empty_iff_false x).mp this




variable (α) in
abbrev Equivclass [Setoid α] := {c : Set α // ∃ x, c =  {y | x ≈ y}}


instance equivclass_setlike : SetLike (Equivclass α) α where
  coe s := s.1
  coe_injective' _ _ h := Subtype.ext h


abbrev quot: α → Equivclass α := fun x => ⟨{y | x ≈ y}, ⟨x,rfl⟩⟩



--scoped notation3 "[[" x "]]" => (Setoid.quot x)

--variable (x : α)
--#check Setoid.quot x

lemma mem_quot (x : α) : x ∈ (Setoid.quot x : Equivclass α)  := by
  --unfold Setoid.quot
  exact Setoid.refl _


lemma mem_quot_iff_equiv (x : α): y ∈ Setoid.quot x ↔ x ≈ y := by
  rfl

lemma mem_quot_iff_equiv' (x : α): y ∈ Setoid.quot x ↔ y ≈ x := by
  rw [mem_quot_iff_equiv]
  exact ⟨Setoid.symm,Setoid.symm⟩

lemma mem_quot_self (x : α): x ∈ Setoid.quot x := by
  exact Setoid.refl x


lemma exist_quot (c : Equivclass α) : ∃ x, c = Setoid.quot x  := by
  obtain ⟨c, x, hx⟩ := c
  use x
  unfold quot
  simp only [hx]

/--
The equivalence relation `≈` is symmetric.
-/
lemma symm_iff {x y : α}: x ≈ y ↔ y ≈ x := ⟨Setoid.symm, Setoid.symm⟩


lemma equiv_iff_of_equiv {x y z : α} (H : x ≈ y) : x ≈ z ↔ y ≈ z := by
  constructor
  intro H2
  exact Setoid.trans (Setoid.symm H) H2
  intro H2
  exact Setoid.trans H H2

lemma equiv_iff_mem_same_class {c : Setoid.Equivclass α}  (H : x ∈ c) :  x ≈ y  ↔  y ∈ c  := by
  obtain ⟨z,hz⟩:= exist_quot c
  rw [hz] at H
  rw [hz]
  rw [mem_quot_iff_equiv] at H
  rw [mem_quot_iff_equiv]
  replace H := Setoid.symm H
  exact Setoid.equiv_iff_of_equiv H

lemma quot_eq_iff_equiv {x y: α} : Setoid.quot x = Setoid.quot y ↔ x ≈ y := by
  constructor
  intro H
  have H2:= Setoid.mem_quot_self y
  rw [<-H] at H2
  rw [Setoid.mem_quot_iff_equiv] at H2
  exact H2
  intro H
  rw [SetLike.ext_iff]
  intro z
  repeat rw [Setoid.mem_quot_iff_equiv]
  exact Setoid.equiv_iff_of_equiv H

lemma mem_quot_iff_eq_quot {x : α} {c : Equivclass α}  : x ∈ c ↔ c = Setoid.quot x:= by
  obtain ⟨y, hy⟩ := exist_quot c
  rw [hy]
  rw [Setoid.mem_quot_iff_equiv]
  symm
  exact Setoid.quot_eq_iff_equiv


lemma quot_nonempty' (c : Equivclass α) : c.1.Nonempty := by
  obtain ⟨z, hz⟩ := exist_quot c
  rw [hz]
  use z
  simp only [Set.mem_setOf_eq, refl]


noncomputable abbrev Equivclass.unquot : Equivclass α → α :=  fun c => (Setoid.quot_nonempty' c).some

lemma Equivclass.unquot_mem {c : Equivclass α} : c.unquot ∈ c := by
  exact Set.Nonempty.some_mem _

@[simp]
lemma Equivclass.quot_unquot_eq {c : Equivclass α}: Setoid.quot c.unquot = c := by
  symm
  rw [<-Setoid.mem_quot_iff_eq_quot]
  exact c.unquot_mem


lemma unquot_quot_equiv : x ≈ (Setoid.quot x).unquot := by
  rw [<-Setoid.quot_eq_iff_equiv]
  rw [Equivclass.quot_unquot_eq]



end Setoid
