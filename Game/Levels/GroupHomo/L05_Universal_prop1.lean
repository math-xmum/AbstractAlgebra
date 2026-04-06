import Game.Metadata
import Game.Generator.Basic

World "GroupHomomorphism"

open QuotientGroup
open scoped Pointwise QuotientGroup
open Pointwise

Level 5

Introduction "
The **universal property** of the quotient group `G/N`:

Let `N` be a normal subgroup of `G` and `π : G →* G/N` the canonical projection.
For any homomorphism `f : G →* H` with `f(n) = 1` for all `n ∈ N`, there exists
a **unique** homomorphism `f' : G/N →* H` such that `f' ∘ π = f`.

In Lean, the canonical quotient map is `QuotientGroup.mk' N`.

This level is substantial: we construct `f'`, prove it is multiplicative,
show `f' ∘ π = f`, and prove uniqueness.
"
variable {G H:Type*} [Group G] [Group H] (N : Subgroup G)

variable (s : G ⧸ N)

#check Subgroup.Normal.conj_mem

Statement [hN : N.Normal] :
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  ∀ f : G →* H,  (∀ n ∈ N, f n = 1) → ∃! f' : (G ⧸ N) →* H, f' ∘ π = f:= by
  Hint "Use `intro f hf` to introduce the homomorphism `f` and the hypothesis that `f`
  kills `N`."
  intro f hf
  Hint "The goal is `∃! f'`, meaning existence and uniqueness. Use `apply ExistsUnique.intro`
  to split it into three sub-goals: (1) construct `f'`, (2) show `f' ∘ π = f`,
  (3) show uniqueness."
  apply ExistsUnique.intro
  pick_goal 3
  Hint "We first construct the map f'. "
  · Hint "We need a group homomorphism `G/N →* H`. Use `apply GroupHom.intro` to split
    the construction into: (1) a map `G/N → H`, and (2) a proof it preserves multiplication."
    apply GroupHom.intro
    pick_goal 2
    · Hint "Use `intro s` to take an element `s : G ⧸ N` (a coset)."
      intro s
      Hint "Each coset `{s}` has a representative `{s}.out : G` (chosen by the axiom of choice).
      Define `f'({s}) := f({s}.out)` by providing the value: `use f (s.out)`"
      use f (s.out)
    · Hint "Use `intro x y` to take two cosets."
      intro x y
      Hint "We need `f((x*y).out) = f(x.out) * f(y.out)`. The key fact is that
      `x.out * y.out` and `(x*y).out` differ by an element of `N`.
      Introduce this with:
      `have hxy : ∃ n ∈ N, x.out * y.out * n = (x*y).out`"
      have hxy : ∃ n ∈ N,   x.out * y.out * n = (x*y).out   := by
        Hint "Use `rw [<-QuotientGroup.mk'_eq_mk']` to convert the goal into a statement
        about the quotient map. Then `simp` closes it since `π(g.out) = g`."
        rw [<-QuotientGroup.mk'_eq_mk']
        Hint "This is now a tautology. Use `simp` to close it."
        simp
      Hint "Unpack `{hxy}` with `obtain ⟨n, hn1, hxyn2⟩ := {hxy}` to get `n ∈ N` and
      `x.out * y.out * n = (x*y).out`."
      obtain ⟨n, hn1, hxyn2⟩ := hxy
      Hint "Rewrite using `{hxyn2}`, expand with `map_mul`, then use `mul_eq_left` and `{hf}`."
      rw [<-hxyn2,map_mul,map_mul]
      rw [mul_eq_left]
      exact hf n hn1
  · Hint "To show two functions are equal, test on each input. Use `ext g`."
    ext g
    Hint "Simplify with `simp` to make the goal readable."
    simp
    Hint "The goal is `f((π g).out) = f(g)`. Since `π(g).out` and `g` represent
    the same coset, they differ by some `n ∈ N`. We need `g * n = (π g).out`."
    suffices hng: ∃ n ∈ N, g*n =  (π g).out
    · Hint "Unpack with `obtain ⟨n, hn1, hn2⟩ := hng`."
      obtain ⟨n, hn1, hn2⟩ := hng
      Hint "Rewrite using `{hn2}`, then expand `f(g * n) = f(g) * f(n) = f(g) * 1 = f(g)`."
      rw [<-hn2]
      Hint "Close with `simp [map_mul, {hf} n hn1]`."
      simp [map_mul,hf n hn1]
    · Hint "We must show `∃ n ∈ N, g * n = (π g).out`. This follows from
      `π(g) = π((π g).out)`, which is a tautology. The relevant lemma is
      `QuotientGroup.mk'_eq_mk'`."
      suffices hqq : π g = π ((π g).out)
      · rw [<-QuotientGroup.mk'_eq_mk']
        exact hqq
      · Hint "This is the tautology `π(g) = π((π g).out)`, known as `Quotient.out_eq'`.
        Use `simp [π]` to close it."
        simp [π]
  · Hint "**Uniqueness:** If `f' ∘ π = f`, then `f'` is determined on all of `G/N`.
    Use `intro f' hf'` then `ext s` to test on each coset."
    intro f' hf'
    Hint "Use `ext s` to compare the two maps element-wise."
    ext s
    Hint "Simplify with `simp`."
    simp
    Hint "Rewrite using `{hf'}` to replace `f` by `f' ∘ π`."
    rw [<-hf']
    Hint "Now `s = π(s.out)` is automatic. Close with `simp [π]`."
    simp [π]



NewTheorem ExistsUnique.intro QuotientGroup.mk'_eq_mk'
