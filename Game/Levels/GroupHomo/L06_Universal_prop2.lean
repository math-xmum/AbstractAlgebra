import Game.Metadata
import Game.Generator.Basic

World "GroupHomomorphism"

open QuotientGroup
open scoped Pointwise QuotientGroup
open Pointwise

Level 6

Introduction "
The universal property **characterizes** the quotient group up to isomorphism.

If two pairs `(P, piP)` and `(Q, piQ)` both satisfy the universal property --
that is, any `f : G →* H` killing `N` factors uniquely through them --
then `P ≃* Q` (they are isomorphic as groups).

We prove this by using each universal property to produce maps `P →* Q` and
`Q →* P`, then showing their compositions are the identity by uniqueness.

This is the longest proof in the world. The key new ideas are `Classical.choose`,
`ExistsUnique.unique`, and `Function.leftInverse_iff_comp`.
"
universe v u

variable {G:Type*} [Group G]  (N : Subgroup G)

noncomputable section


Statement [hN : N.Normal] {Q P:Type u} [Group Q] [Group P] (piP : G →* P) (piQ : G →* Q) (hP : ∀ n∈ N, piP n = 1) (hQ : ∀ n ∈ N, piQ n = 1)
  (hPu: ∀ {H : Type u} [gH :Group H], ∀ f : G →* H,  (∀ n ∈ N, f n = 1) → ∃! f' : P →* H, f' ∘ piP = f)
  (hQu: ∀ {H : Type u} [gH: Group H], ∀ f : G →* H,  (∀ n ∈ N, f n = 1) → ∃! f' : Q →* H, f' ∘ piQ = f) : ∃! psi : P ≃* Q, psi ∘ piP = piQ   := by
    Hint "Apply the universal property of `P` to the map `{piQ}` (which kills `N` by `{hQ}`):
    `have HP := (hPu piQ hQ)`
    This gives `HP : ∃! f', f' ∘ piP = piQ`."
    have HP := (hPu piQ hQ)
    Hint "Similarly, apply the universal property of `Q` to `{piP}`:
    `have HQ := (hQu piP hP)`"
    have HQ:= (hQu piP hP)
    /-
    Hint "
    For a proposition p : α → Prop, ∃! x:α , p x = ∃ x: α, p α ∧ ∀ y:α, p y → x = y.

    We unpack the ExistsUnique claim {HP} to get a group homomorphism toFun : P→*Q. Here is a ticky point: one can not use `obtain` to unpack. Since `obtain` is for proof manipulation only,
    i.e. when the goal is a proposition.
      In our case, the goal is a multiplicative equivalence, which is not a proposition.

      The solution is to use the axiom of choice to pick the element.
      Try
      `let toFun := Classical.choose HP`
      "
    Hint "Now use `Classical.choose_spec` to extract the assertion that the function {toFun} satisfies the property `{toFun} ∘ ⇑piP = ⇑piQ`.
    This is the first part of the ExistsUnique claim {HP}. One can use
    `have HtoFun := (Classical.choose_spec HP).1`
    "
    -/
    Hint "Recall `∃! x, p x` unfolds to `∃ x, p x ∧ ∀ y, p y → y = x`.
    Unpack `HP` with `obtain ⟨toFun, HtoFun, HtoFun'⟩ := HP` to get:
    - `toFun : P →* Q`
    - `HtoFun : toFun ∘ piP = piQ`
    - `HtoFun' : ∀ y, y ∘ piP = piQ → y = toFun`"
    obtain ⟨toFun,HtoFun, HtoFun'⟩  :=  HP
    Hint "Do the same for `HQ`: `obtain ⟨invFun, HinvFun, HinvFun'⟩ := HQ`"
    obtain ⟨invFun, HinvFun, HinvFun'⟩ := HQ
    Hint "The hypotheses may contain lambda expressions like `(fun x => f x) y`. The
    `beta_reduce` tactic simplifies these to `f y`. Apply it everywhere:
    `beta_reduce at *`"
    beta_reduce at *
    Hint "Preparation is done. Use `constructor` to split the goal into constructing the
    equivalence and proving its properties."
    constructor
    pick_goal 2
    Hint "Use `pick_goal 2` to work on the equivalence construction first."
    · Hint "Build the multiplicative equivalence with:
      `apply MulEquiv.intro toFun invFun`
      This requires showing `invFun ∘ toFun = id` (left inverse) and
      `toFun ∘ invFun = id` (right inverse), plus multiplicativity."
      apply MulEquiv.intro toFun invFun
      · Hint "**Left inverse:** Both `id` and `invFun ∘ toFun` are homomorphisms `P →* P`
        that factor `piP` through `piP`. By uniqueness, they must be equal.
        Use `ExistsUnique.unique`:
        `have HPid := (hPu piP hP).unique (y₁:=MonoidHom.id P) (y₂ :=MonoidHom.comp invFun toFun) ?_ ?_`
        The `?_ ?_` placeholders become sub-goals to fill in."
        have HPid := (hPu piP hP).unique (y₁:=MonoidHom.id P) (y₂ :=MonoidHom.comp invFun toFun) ?_ ?_
        Hint "Rewrite the goal to function composition form:
        `rw [Function.leftInverse_iff_comp]`"
        rw [Function.leftInverse_iff_comp]
        Hint "In Lean, `MonoidHom` composition and function composition are different.
        Use `rw [<-MonoidHom.coe_comp]` to bridge them, then `rw [<-HPid]`."
        rw [<-MonoidHom.coe_comp]
        Hint "Now apply `{HPid}` with `rw [<-{HPid}]`, then close with `rfl`."
        rw [<-HPid]
        rfl
        · Hint "`id ∘ piP = piP` is trivially `rfl`."
          rfl
        · Hint "Show `(invFun ∘ toFun) ∘ piP = piP`. First convert with `rw [MonoidHom.coe_comp]`,
          then use associativity: `rw [Function.comp_assoc]`.
          Finally rewrite with `{HtoFun}` and `{HinvFun}`."
          rw [MonoidHom.coe_comp]
          rw [Function.comp_assoc]
          rw [HtoFun,HinvFun]
      · Hint "**Right inverse:** The argument mirrors the left inverse proof, using
        the uniqueness from `hQu` instead. Try it yourself!"
        have HQid :=  (hQu piQ hQ).unique (y₁:=MonoidHom.id Q) (y₂ :=MonoidHom.comp toFun invFun) ?_ ?_
        rw [Function.rightInverse_iff_comp]
        rw [<-MonoidHom.coe_comp,<-HQid]
        ext;simp
        · ext;simp
        · simp_all
          rw [Function.comp_assoc,HinvFun,HtoFun]
      · Hint "Multiplicativity comes for free since `toFun` is a `MonoidHom`.
        Use `exact toFun.map_mul`."
        exact toFun.map_mul
    Hint "Now prove the properties of the equivalence. Use `simp` to simplify the goal."
    simp
    Hint "Use `constructor` to split into the factorization property and uniqueness."
    constructor
    · Hint "The first part is exactly `{HtoFun}`. Use `rw [{HtoFun}]`."
      rw [HtoFun]
    · Hint "For uniqueness, introduce `y` and its property with `intro y hy`, then
      specialize: `specialize {HtoFun'} y hy`."
      intro y hy
      Hint "Specialize `{HtoFun'}` to `{y}` and `{hy}`."
      specialize HtoFun' y hy
      Hint "Close with `simp [<-{HtoFun'}]`."
      simp [<-HtoFun']





NewTheorem MonoidHom.coe_comp MonoidHom.id MonoidHom.comp Function.comp_assoc

section
