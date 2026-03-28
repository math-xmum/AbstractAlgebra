import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 12

Introduction "
Let H be a subgroup of G.
The subset g • H := {gh | h∈H} for some g∈G is called a left coset of H.

Basically all cosets are essentially the same in the sense that there is a natural bijection between g H and k H for arbitrary g k ∈ G.

In Lean, a bijection between two types α and β is represented by the type `Equiv α β'
"

open Monoid Group

variable {G : Type*} [Group G] {g k:G} {H : Set G}


open scoped Pointwise
open Pointwise

--instance : HSMul G (Set G) (Set G):=inferInstance

Statement :
  Equiv (g • H :Set G) (k • H : Set G):= by
  Hint "Use `constructor' to expend the definition of Equiv"
  refine ⟨?_, ?_, ?_, ?_⟩
  Hint "Pick the 1st goal, which required to define a map from g • H to k • H"
  · Hint " Define the map g • H ∋ x ↦ (k * g⁻¹)*x. On can achive this by using `use fun x => ⟨(k * g⁻¹)*x, ?_⟩'
    Here we need to prove that the function is well defined, i.e.  `(k * g⁻¹)*x ∈ k • H'
    "
    exact fun x => ⟨(k * g⁻¹)*x, by
      obtain ⟨h,b,hh⟩ := x.2
      simp at hh
      rw [<-hh]
      group
      use h
      trivial⟩
  Hint "Now construct the inverse function"
  · Hint "This is the same as the first case. We let you to practice by yourself."
    exact fun x => ⟨(g * k⁻¹)*x, by
      obtain ⟨h,b,hh⟩ := x.2
      simp at hh
      rw [<-hh]
      group
      use h
      trivial⟩
  · Hint "`Function.LeftInverse g f' means ∀ x, g (f x) = x. So we use `intro' to reveal the goal. "
    intro x
    Hint "Since `x' is a subtype, `y = x' if and only if the `y.1 = x.1'. Use `ext' to reduced the problem to comparing the values hold in  y and x. "
    ext
    Hint "Use `simp' to clear up the goal"
    simp
    Hint "Use `group' to finish the proof. "
    group
  · Hint "This is similar to the pervious case."
    intro x
    ext;group


NewTheorem Set
