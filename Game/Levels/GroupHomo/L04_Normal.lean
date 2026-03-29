import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "GroupHomomorphism"

open scoped Pointwise
open Pointwise

Level 4

Introduction "
A subgroup N of G is called a normal subgroup if
∀ g n, n ∈ N → g*n*g⁻¹ ∈ N.

We will show that N is normal if and only if the multiplication of any two left cosets is still a left coset.

In this case, the equation (g • N) * (h • N) = (g*h) • N must holds since g*h is in (g • N) * (h • N).

By this property,
we see that
the map G → Set G sending g to gN is a monoid homomorphism, whose image is the set G/N of left cosets of N.
We call π : G → G/N canonical  group homomorphism.

"
variable {G H:Type*} [Group G] (N : Subgroup G)

#check Subgroup.Normal.conj_mem

private lemma normal_coset_mul_sub {g h x : G} (hN : N.Normal)
    (hx : x ∈ (g • (N : Set G)) * (h • N)) : x ∈ (g * h) • (N : Set G) := by
  rw [Set.mem_mul_set_iff] at hx
  obtain ⟨a, b, ⟨n1, hn1, rfl⟩, ⟨n2, hn2, rfl⟩, hab⟩ := hx
  use (h⁻¹ * n1 * h * n2)
  constructor
  · apply Subgroup.mul_mem _ _ hn2
    nth_rw 2 [<-inv_inv h]
    exact Subgroup.Normal.conj_mem hN _ hn1 _
  · simp [<-hab]; group

private lemma coset_mul_sup {g h x : G}
    (hx : x ∈ (g * h) • (N : Set G)) : x ∈ (g • (N : Set G)) * (h • N) := by
  obtain ⟨n, hn, rfl⟩ := hx
  rw [Set.mem_mul_set_iff]
  exact ⟨g, h * n, ⟨1, Subgroup.one_mem N, by simp⟩, ⟨n, hn, rfl⟩, by group⟩

private lemma coset_mul_imp_normal
    (H : ∀ g h : G, (g • (N : Set G)) * (h • N) = (g * h) • N) : N.Normal := by
  constructor
  intro n hn g
  specialize H g (g⁻¹)
  simp at H
  rw [<-SetLike.mem_coe, <-H, Set.mem_mul]
  exact ⟨g * n, ⟨n, hn, rfl⟩, g⁻¹, ⟨1, by simp [Subgroup.one_mem], by simp⟩, by simp⟩

Statement : N.Normal ↔ ∀ g h : G,  (g • (N :Set G)) * (h • N) = (g * h) • N := by
  Hint "Use `constructor` to split the statement into two directions."
  constructor
  · Hint "Introduces all the necessary hypotheses and free variables."
    intro H g h
    Hint "To prove to sets equal, we need to prove that an element in one set if and only if it is in the other set.
    We can use the `ext` tactic to rewrite the goal."
    ext x
    Hint "Use constructor to split the statement into two directions."
    constructor
    · Hint "Introduces all the necessary hypotheses and free variables."
      intro hx
      exact normal_coset_mul_sub N H hx
    · Hint "Introduce the hypothesis."
      intro hx
      exact coset_mul_sup N hx
  · Hint "Introduce the hypothesis."
    intro H
    Hint "How can we prove `N.Normal` from the coset multiplication property?
    We need to show ∀ n ∈ N, ∀ g, g * n * g⁻¹ ∈ N.
    Try specializing the hypothesis with `g` and `g⁻¹`."
    exact coset_mul_imp_normal N H


open scoped Pointwise

NewTheorem MonoidHom.mem_ker inv_inv Set.mem_mul_set_iff Subgroup.Normal.conj_mem Subgroup.one_mem Subgroup.mul_mem Set.mem_prod SetLike.mem_coe
