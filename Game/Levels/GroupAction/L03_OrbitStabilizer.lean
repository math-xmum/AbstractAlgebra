import Game.Metadata
-- import Mathlib

World "GroupAction"

Level 3

Introduction "
The **Orbit-Stabilizer theorem** (set-theoretic version): for any `x : X`,
the map `gG_x ↦ g • x` is a bijection `G/G_x → orbit G x`.

We construct this bijection using `Equiv.ofBijective`, which takes a function
and a proof that it is both injective and surjective.

Key theorems: `MulAction.mem_orbit`, `MulAction.mem_stabilizer_iff`,
`QuotientGroup.mk_out_eq_mul`, `inv_smul_smul`, `QuotientGroup.eq`.
"

open Pointwise
open scoped Pointwise
open scoped MulAction
open MulAction

variable {G X:Type*} [Group G] [MulAction G X]

#check  QuotientGroup.mk_out_eq_mul

Statement (x : X) : Nonempty (G ⧸  stabilizer G x ≃ orbit G x)  := by
  Hint "We prove existence of a bijection. Use `apply Nonempty.intro` then
  `apply Equiv.ofBijective` to reduce to: (1) define the map, and (2) prove bijectivity.
  Use `pick_goal 2` to handle the map construction first."
  apply Nonempty.intro
  apply Equiv.ofBijective
  pick_goal 2
  · Hint "Use `intro y` to take a coset `y : G ⧸ stabilizer G x`."
    intro y
    Hint "Map `{y}` to `{y}.out • x` (where `.out` picks a representative). Use `use {y}.out • x`."
    use y.out • x
    Hint "Show `{y}.out • x ∈ orbit G x` with `apply MulAction.mem_orbit`."
    apply MulAction.mem_orbit
  Hint "Now prove bijectivity. Use `constructor` to split into injectivity and surjectivity."
  constructor
  · Hint "**Injectivity:** Use `intro y1 y2` then `simp` to simplify, then `intro H`
    to assume `y1.out • x = y2.out • x`."
    intro y1 y2
    simp only [Subtype.mk.injEq]
    intro H
    Hint "Apply `y2.out⁻¹` to both sides: `apply_fun (y2.out⁻¹ • ·) at {H}`.
    This is a common trick -- applying an invertible group element to cancel."
    apply_fun (y2.out⁻¹ • ·) at H
    Hint "Simplify with `simp only [inv_smul_smul] at {H}` to get `y2.out⁻¹ • (y1.out • x) = x`."
    simp only [inv_smul_smul] at H
    Hint "Rewrite `{H}` using `mul_smul` to get `(y2.out⁻¹ * y1.out) • x = x`, then
    convert to stabilizer membership with `MulAction.mem_stabilizer_iff`:
    `rw [<-mul_smul, <-MulAction.mem_stabilizer_iff] at {H}`"
    rw [<-mul_smul,<-MulAction.mem_stabilizer_iff] at H
    Hint "Now `{H}` says `y2.out⁻¹ * y1.out ∈ stabilizer G x`, which means `[y1] = [y2]`
    in the quotient. Use `rw [<-QuotientGroup.eq] at {H}` then `simp at {H}`."
    rw [<-QuotientGroup.eq] at  H
    simp only [QuotientGroup.out_eq'] at H
    Hint "Now `{H} : y1 = y2`. Use `rw [{H}]`."
    rw [H]
  · Hint "**Surjectivity:** Use `intro ⟨y, hy⟩` to take an element of the orbit (a subtype)."
    intro ⟨y,hy⟩
    Hint "Unpack `hy` to get `g : G` with `g • x = y`: `obtain ⟨g, hg⟩ := hy`"
    obtain ⟨g,hg⟩ := hy
    Hint "Use `beta_reduce at {hg}` to simplify any lambda expressions."
    beta_reduce at hg
    Hint "Simplify the goal with `simp only [Subtype.mk.injEq]`, then provide the preimage: `use g`
    (Lean auto-coerces `g` to its coset `[g] : G ⧸ stabilizer G x`)."
    simp only [Subtype.mk.injEq]
    use g
    Hint "The representative `[g].out` may differ from `g` by a stabilizer element.
    Use `have hqg : ∃ (h : stabilizer G x), (g : G ⧸ stabilizer G x).out = g * h := QuotientGroup.mk_out_eq_mul _ _`"
    have hqg : ∃ (h : stabilizer G x), (g: G ⧸  stabilizer G x).out = g * h := QuotientGroup.mk_out_eq_mul _ _
    Hint "Unpack with `obtain ⟨h, hh⟩ := hqg`."
    obtain ⟨h, hh⟩ := hqg
    Hint "Rewrite using `{hh}` and `mul_smul`, then use `MulAction.mem_stabilizer_iff.1 h.2`
    to replace `h • x` by `x`. Finally `exact {hg}` closes the goal."
    rw [hh,mul_smul]
    rw [MulAction.mem_stabilizer_iff.1 h.2]
    exact hg



NewTheorem QuotientGroup.mk_out_eq_mul Equiv.ofBijective MulAction.mem_orbit MulAction.mem_stabilizer_iff SemigroupAction.mul_smul Equiv.ofBijective MulAction.stabilizer MulAction.orbit inv_smul_smul QuotientGroup.eq
-- NewTactic moved to BasicLean
