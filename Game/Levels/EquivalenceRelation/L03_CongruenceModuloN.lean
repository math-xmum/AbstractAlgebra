import Game.Metadata
import Game.Generator.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 3


variable {S :Type*}



Statement (preamble := constructor ) (n : ℤ): Equivalence (α := ℤ) (fun a b => n ∣ (a - b)) := by
  intro x
  rw [sub_self]
  exact dvd_zero n
  intro x y hxy
  have H : - (x - y) = y-x := neg_sub _ _
  rw [<-H]
  rw [dvd_neg]
  exact hxy
  intro x y z hxy hyz
  have H : (x - y) + (y - z) = x - z := sub_add_sub_cancel _ _ _
  rw [<-H]
  exact dvd_add hxy hyz


NewTactic «intro» rfl rw exact simp «have» 
OnlyTactic intro rfl rw exact simp «have»
