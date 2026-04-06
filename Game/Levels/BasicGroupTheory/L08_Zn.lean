import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 8

Introduction "Let $\\mathbb{Z}_n$ be the set of integers modulo $n$, represented as `Fin n` in Lean. In this level, we construct a **commutative group** (abelian group) structure on `Fin n` with addition modulo $n$.

We use `CommGroup_mk` to build the group by verifying each axiom: associativity, identity, inverses, and commutativity. Each subgoal requires simplifying modular arithmetic expressions using `simp`, `ext`, and arithmetic lemmas like `Nat.mod_eq_of_lt`."
open Monoid

variable {n: ℕ+}

def CommGroup_mk {G : Type*}
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
  inv_mul_cancel := add_left_inv
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
      Hint "Unfold the local definition `add` using `simp [add]` to expand the goal."
      simp only [add]
      Hint "The goal compares two `Fin n` values. Use `ext` to reduce it to comparing their underlying natural numbers."
      ext
      Hint "Use `simp only` to simplify, then `exact Nat.mod_eq_of_lt a.2` to finish (since `a.1 < n` means `a.1 % n = a.1`)."
      simp only [Nat.add_zero]
      exact Nat.mod_eq_of_lt a.2
    · intro a
      simp only [add, zero]
      ext
      simp only [Nat.zero_add]
      exact Nat.mod_eq_of_lt a.2
    · intro a b c
      simp only [add, Nat.mod_add_mod, Nat.add_mod_mod, Fin.mk.injEq]
      Hint "Use `rw [add_assoc]` to apply associativity of natural number addition."
      rw [add_assoc]
    · intro a
      Hint "Unfold the definitions of `add` and `neg` with `simp [add, neg]`, then `rfl` finishes."
      simp only [add, neg, zero]
      ext
      simp only
      rw [Nat.mod_add_mod]
      rw [Nat.sub_add_cancel (le_of_lt a.2)]
      exact Nat.mod_self n
    · intro a b
      simp only [add, Fin.mk.injEq]
      Hint "Use `rw [add_comm]` to apply commutativity of natural number addition."
      rw [add_comm]


NewTheorem CommGroup_mk ext_lemma add_assoc add_comm Nat.mod_succ_eq_iff_lt Fin.is_lt Nat.mod_add_mod  Nat.add_mod_mod  Fin.mk.injEq Fin.is_le' Nat.sub_add_cancel Nat.mod_self Fin.zero_eta Nat.add_comm Nat.pos_of_ne_zero Nat.mod_eq_of_lt
NewDefinition add neg zero
