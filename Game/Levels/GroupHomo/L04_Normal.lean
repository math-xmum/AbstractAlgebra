import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "GroupHomomorphism"

open scoped Pointwise
open Pointwise

Level 4

Introduction "
A subgroup `N` of `G` is **normal** if `∀ g n, n ∈ N → g * n * g⁻¹ ∈ N`.

We prove: `N` is normal if and only if the product of any two left cosets
is again a left coset, i.e., `(g • N) * (h • N) = (g * h) • N`.

This is what makes the quotient `G/N` into a group: coset multiplication
is well-defined precisely when `N` is normal. The resulting map
`π : G → G/N` is the **canonical group homomorphism**.

This is a longer proof. Take it step by step!
"
variable {G H:Type*} [Group G] (N : Subgroup G)

#check Subgroup.Normal.conj_mem

Statement : N.Normal ↔ ∀ g h : G,  (g • (N :Set G)) * (h • N) = (g * h) • N := by
  Hint "The goal is an `↔`. Use `constructor` to split it into the forward (`→`) and
  backward (`←`) directions."
  constructor
  · Hint "Use `intro H g h` to introduce the normality hypothesis and two group elements."
    intro H g h
    Hint "To prove two sets are equal, show they have the same elements. The `ext x`
    tactic reduces `A = B` to `x ∈ A ↔ x ∈ B`."
    ext x
    Hint "Use `constructor` to split the `↔`."
    constructor
    · Hint "Use `intro hx` to assume `x ∈ (g • N) * (h • N)`."
      intro hx
      Hint "Rewrite `{hx}` using `Set.mem_mul_set_iff` to express membership as:
      there exist `a ∈ g • N` and `b ∈ h • N` with `a * b = x`.
      `rw [Set.mem_mul_set_iff] at {hx}`"
      rw [Set.mem_mul_set_iff] at hx
      Hint "Use `obtain` to unpack `{hx}` into elements and their properties:
      `obtain ⟨a, b, ha, hb, hab⟩ := {hx}`"
      obtain ⟨a, b, ha, hb,hab⟩ := hx
      Hint "Unpack `{ha} : a ∈ g • N` to get `n1 ∈ N` with `g * n1 = a`:
      `obtain ⟨n1, hn1, ha : g * n1 = a⟩ := {ha}`"
      obtain ⟨n1, hn1, ha : g*n1 = a ⟩ := ha
      Hint "Similarly unpack `{hb}` to get `n2 ∈ N` with `h * n2 = b`:
      `obtain ⟨n2, hn2, hb : h * n2 = b⟩ := {hb}`"
      obtain ⟨n2, hn2, hb : h*n2 = b ⟩ := hb
      Hint "We need to show `x ∈ (g * h) • N`, i.e., find `n ∈ N` with `(g*h)*n = x`.
      Note `(g*h) * (h⁻¹ * n1 * h * n2) = g * n1 * (h * n2) = a * b = x`.
      So provide the witness: `use h⁻¹ * n1 * h * n2`"
      use (h⁻¹ * n1 * h * n2)
      Hint "Use `constructor` to split into: (1) the witness is in `N`, and (2) the product equals `x`."
      constructor
      · Hint "Since `n2 ∈ N`, it suffices to show `h⁻¹ * n1 * h ∈ N`. Use `Subgroup.mul_mem`
        to split the product: `apply Subgroup.mul_mem _ _ hn2`"
        apply Subgroup.mul_mem  _ _ hn2
        Hint "We need `h⁻¹ * n1 * h ∈ N`. Normality says `g * n * g⁻¹ ∈ N`, so
        rewrite `h` as `(h⁻¹)⁻¹` using `inv_inv`: `nth_rw 2 [<-inv_inv h]`"
        --have hnh : h⁻¹ * n1 * h =  h⁻¹ * n1 * (h⁻¹)⁻¹ := by group
        nth_rw 2 [<-inv_inv h]
        Hint "Now apply `Subgroup.Normal.conj_mem H` to use the normality hypothesis."
        apply Subgroup.Normal.conj_mem H
        Hint "The remaining goal is `n1 ∈ N`, which is exactly `{hn1}`. Use `exact {hn1}`."
        exact hn1
      · Hint "This is a direct computation from `{hab}`, `{ha}`, `{hb}` and group laws."
        simp [<-hab,<-ha,<-hb];group
    · Hint "Use `intro H` to assume `x ∈ (g * h) • N`."
      intro H
      Hint "Unpack `{H}` to get `n ∈ N` with `g * h * n = x`:
      `obtain ⟨n, hn, hx : g * h * n = x⟩ := {H}`"
      obtain ⟨n, hn,hx : g*h*n = x⟩ := H
      Hint "Rewrite the goal using `Set.mem_mul_set_iff` to express membership as a product."
      rw [Set.mem_mul_set_iff]
      Hint "We need `a ∈ g • N` and `b ∈ h • N` with `a * b = x`.
      Choose `a = g` and `b = h * n`: `use g, (h * n)`"
      use g,(h*n)
      Hint "Use `constructor` to split the goal."
      constructor
      · Hint "Show `g ∈ g • N` by writing `g = g * 1` and noting `1 ∈ N`."
        use 1
        Hint "The automation `aesop` closes this."
        aesop
      · Hint "Use `constructor` to split the remaining conjunct."
        constructor
        · Hint "Show `h * n ∈ h • N` using the witness `n`."
          use n; aesop
        · Hint "The equation `g * (h * n) = x` follows from `{hx}` by associativity."
          rw [<-hx];group
  · Hint "Use `intro H` to assume the coset multiplication property. Then `constructor`
    to begin constructing the `Normal` instance."
    intro H
    Hint "Use `constructor` to start the proof of normality."
    constructor
    Hint "Use `intro n hn g` to introduce the element, its membership, and the conjugator."
    intro n hn g
    Hint "Specialize the coset hypothesis to `g` and `g⁻¹`:
    `specialize H g (g⁻¹)`. This gives `(g • N) * (g⁻¹ • N) = (g * g⁻¹) • N`."
    specialize H g (g⁻¹)
    Hint "Simplify `g * g⁻¹` to `1` with `simp at H`."
    simp at H
    Hint "**Subtlety:** `g * n * g⁻¹ ∈ N` (subgroup membership) is different from
    `g * n * g⁻¹ ∈ ↑N` (set membership). The coercion `↑N = (N : Set G)` is the
    underlying set. Use `rw [<-SetLike.mem_coe]` to switch to set membership."
    rw [<-SetLike.mem_coe]
    Hint "Now `rw [<-H]` rewrites `↑N` to `(g • N) * (g⁻¹ • N)`."
    rw [<-H]
    Hint "Use `rw [Set.mem_mul]` to express membership as a product of two elements."
    rw [Set.mem_mul]
    Hint "Provide the first element `g * n` from `g • N`: `use g * n`"
    use g*n
    Hint "Use `constructor` to split the goal."
    constructor
    · exact ⟨n,hn,rfl⟩
    · Hint "Provide the second element `g⁻¹` from `g⁻¹ • N`: `use g⁻¹`"
      use g⁻¹
      Hint "Use `constructor` to split."
      constructor
      · Hint "Show `g⁻¹ ∈ g⁻¹ • N` by writing `g⁻¹ = g⁻¹ * 1` and using `Subgroup.one_mem`."
        exact ⟨1, Subgroup.one_mem _, mul_one _⟩
      · Hint "The equation `g * n * g⁻¹ = (g * n) * g⁻¹` is group arithmetic. Use `group`."
        group


open scoped Pointwise

NewTheorem MonoidHom.mem_ker Set.mem_mul_set_iff Subgroup.Normal.conj_mem Subgroup.one_mem Subgroup.mul_mem Set.mem_prod SetLike.mem_coe
