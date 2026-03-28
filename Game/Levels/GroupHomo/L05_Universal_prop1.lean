import Game.Metadata
import Game.Generator.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

World "GroupHomomorphism"

open QuotientGroup
open scoped Pointwise QuotientGroup
open Pointwise

Level 5

Introduction "
We now explore the universal property of quotient group.

Let N be a normal subgroup of G and π : G →* N is the canonical projection.
Then
(*)    ∀ group homomorphism f : G →* H such that f(N) = 1 → ∃! f' : G/N →* H such that f' ∘ π = f.

This is the defining property of the quotient group, in the sense that if (Q, π' : G →* Q) is a pair of group and group homomorphism satisfies (*) (with π replaced by π'), then there is a unique group isomorphism q : G/N →* Q such that π' = q ∘ π.


In Mathlib, the canonical quotient map is called
QuotientGroup.mk'
We now prove the first claim.


"
variable {G H:Type*} [Group G] [Group H] (N : Subgroup G)

variable (s : G ⧸ N)

#check Subgroup.Normal.conj_mem

Statement [hN : N.Normal] :
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  ∀ f : G →* H,  (∀ n ∈ N, f n = 1) → ∃! f' : (G ⧸ N) →* H, f' ∘ π = f:= by
  Hint "Introduce all the hypothesis and free variables."
  intro f hf
  Hint "`∃!` means existence and uniqueness. We can use `apply ExistsUnique.intro` to split it into three goals. One also can use `constructor` but then the goal will be split into two parts. "
  haveI := hN
  refine ExistsUnique.intro ?_ ?_ ?_
  Hint "We first construct the map f'. "
  pick_goal 1
  · Hint "We should first construct a map  G/N → H and then show that it is multiplicative. Use `GroupHom.intro` to split the goal"
    refine MonoidHom.mk' (fun s => f (s.out)) ?_
    Hint "Introduce all varaibles."
    intro x y
    dsimp only
    Hint "We observe that {x}.out * {y}.out *n = ({x}*{y}).out.
    Use `have hxy : ∃ n ∈ N,   x.out * y.out * n = (x*y).out`
    to introduce the goal.
    "
    have hxy : ∃ n ∈ N,   x.out * y.out * n = (x*y).out   := by
      Hint "Now use `QuotientGroup.mk'_eq_mk'`"
      rw [<-QuotientGroup.mk'_eq_mk']
      Hint "The it is a tautology since π = (mk' N) is a group homomorphism and π (x.out) = x. Using `simp` can close the goal. "
      simp
    Hint "The rest is clear by combining {hf} and {hxy}.
    First introduce n and assumptions it satisfies in {hxy}.
    One can use `obtain`. Then rewrite the goal using the assumptions and {hf}. "
    obtain ⟨n, hn1, hxyn2⟩ := hxy
    Hint "The proof can be finished by using {hf}"
    rw [<-hxyn2,map_mul,map_mul]
    rw [mul_eq_left]
    exact hf n hn1
  · Hint "We only need to test the equality on each element g in G. Use `ext` tactic "
    ext g
    Hint "Try to simp the goal"
    simp
    Hint "
    This is similar to the proof of map_mul in the construction of
    G⧸N →* H.

    To prove the goal it suffice to show that  (π {g}).out = {g} * n for some n in N.
    Since then f ((π {g}).out) = f (g *n)
    = f(g) * f(n) = f(g) * 1 = f(g).
    "
    suffices hng: ∃ n ∈ N, g*n =  (π g).out by
      Hint "Now obtain n and  g * n = (π g).out use `obtain ⟨n, hn1, hn2⟩ := hng`. "
      obtain ⟨n, hn1, hn2⟩ := hng
      Hint "Rewrite the goal using {hn2}."
      rw [<-hn2]
      Hint "The rest part of the proof of the sub goal is easy by using {hf}. "
      simp [map_mul,hf n hn1]
    · Hint " It suffices to show that
      π (g) = π ((π g).out) which is a tautology. In fact,
      g N = (π g).out N if and only if
      g  * n = (π g).out for some n∈N.
      This is a lemma  called `QuotientGroup.mk'_eq_mk'`.
      "
      suffices hqq : π g = π ((π g).out) by
        rw [<-QuotientGroup.mk'_eq_mk']
        exact hqq
      Hint " By the definition of π, this is tautology, called `Quotient.out_eq'` in Mathlib. Use `simp [{π}]` will close the goal. "
      simp [π]
  · Hint "Now we show the uniqueness part. This is again a tautology. First introduce the variables and hypothesises. "
    intro f' hf'
    Hint "Use `ext s`"
    ext s
    Hint "Simplify the goal. "
    simp
    Hint "Rewrite f by hf'"
    rw [<-hf']
    Hint "Again we use s = π (s.out), which is automatically simplified by `simp [{π}]`. "
    simp [π]



NewTheorem ExistsUnique.intro QuotientGroup.mk'_eq_mk'
