import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 9

Introduction "
Let Z_n be the set of integers modulo $n$.
Then Z_n form a commutative group (i.e. an Abelian group).
"
open Monoid

variable {n: ℕ+}

lemma CommGroup_mk {G : Type*}
(add: G → G → G) (zero : G)
(neg: G → G)
(add_zero: ∀ a, add a zero = a) (zero_add: ∀ a, add zero a = a) (add_assoc: ∀ a b c, add (add a b) c = add a (add b c))
(add_left_inv: ∀ a, add (neg a) a = zero) (add_comm: ∀ a b, add a b = add b a) : CommGroup G where
  mul := add
  one := zero
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  inv := neg
  mul_left_inv := add_left_inv
  mul_comm := add_comm

@[simp]
lemma ext_lemma (a b: Fin (n+1)):  a = b ↔ a.1 = b.1:= by
  constructor
  . omega
  intro h
  ext; exact h


Statement {n : ℕ} {hn : n ≠ 0} {hn' : 0<n}:
 let add (a b : Fin (n)): Fin (n) := ⟨(a.1+b.1)%(n), by apply Nat.mod_lt;exact hn'⟩
 let zero : Fin n := ⟨0, hn'⟩
 let neg (a :Fin (n)): Fin (n) := ⟨(n -a)%(n), by apply Nat.mod_lt;exact hn'⟩
 CommGroup (Fin (n)) :=
  by
    apply CommGroup_mk add zero neg
    · intro a
      Hint "Use the definition to simplify the goal.
      You can use `simp [add]' "
      simp [add]
      Hint "Use `ext' tactic"
      ext
      Hint "Use `simp' to simplify the goal"
      simp only
      apply (Nat.mod_eq_iff_lt hn).2
      exact a.2
    · intro a
      simp [add]
      ext
      apply (Nat.mod_eq_iff_lt hn).2
      exact a.2
    · intro a b c
      simp only [add, Nat.mod_add_mod, Nat.add_mod_mod, Fin.mk.injEq]
      Hint "Use `add_assoc' "
      rw [add_assoc]
    · intro a
      Hint "Use the definition of neg"
      simp [add,neg]
    · intro a b
      simp only [add, Fin.mk.injEq]
      Hint "Use `add_comm' "
      rw [add_comm]


NewTactic use rw rfl apply group constructor intro ext simp simp_rw linarith exact
NewTheorem CommGroup_mk ext_lemma add_assoc add_comm Nat.mod_succ_eq_iff_lt Fin.is_lt Nat.mod_add_mod  Nat.add_mod_mod  Fin.mk.injEq Fin.is_le' Nat.sub_add_cancel Nat.mod_self Fin.zero_eta Nat.add_comm Nat.not_eq_zero_of_lt Nat.mod_eq_iff_lt
NewDefinition add neg zero
