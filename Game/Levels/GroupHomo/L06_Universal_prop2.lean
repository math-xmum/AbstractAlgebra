import Game.Metadata
import Game.Generator.Basic

World "GroupHomomorphism"

open QuotientGroup
open scoped Pointwise QuotientGroup
open Pointwise

Level 6

Introduction "
This universal property characterizes the quotient group in the following sense:
any pairs (Q, π : G →* Q) satisfying the following properties are canonically isomorphic to each other:

(*1) N ≤ ker π
(*2) For any group homomorphism f : G →* H such that f(N) = 1, there exists a unique homomorphism f' : Q →* H such that f' ∘ π = f.

In this section, we will prove this claim.

Note that in the previous level, we established that the pair (G/N, π : G →* G/N) satisfies the universal property (*), i.e., the quotient group exists.
"
universe v u

variable {G:Type*} [Group G]  (N : Subgroup G)

noncomputable section


Statement [hN : N.Normal] {Q P:Type u} [Group Q] [Group P] (piP : G →* P) (piQ : G →* Q) (hP : ∀ n∈ N, piP n = 1) (hQ : ∀ n ∈ N, piQ n = 1)
  (hPu: ∀ {H : Type u} [gH :Group H], ∀ f : G →* H,  (∀ n ∈ N, f n = 1) → ∃! f' : P →* H, f' ∘ piP = f)
  (hQu: ∀ {H : Type u} [gH: Group H], ∀ f : G →* H,  (∀ n ∈ N, f n = 1) → ∃! f' : Q →* H, f' ∘ piQ = f) : ∃! psi : P ≃* Q, psi ∘ piP = piQ   := by
    Hint "Begin with the hypothesis hPu. Instantiate hPu with the group homomorphism {piQ} and the condition {hQ} to obtain a unique factorization HP through {piP}.
    Try `have HP := (hPu piQ hQ) `"
    have HP := (hPu piQ hQ)
    Hint "Similarly, instantiate hQu with the group homomorphism {piP} and the condition {hP} to obtain a unique factorization HQ through {piQ}."
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
    Hint "
    For a proposition p : α → Prop, ∃! x:α , p x = ∃ x: α, p α ∧ ∀ y:α, p y → x = y.
    Use ` obtain ⟨toFun,HtoFun, HtoFun'⟩  :=  HP`
    to obtain toFun and its properties.
    "
    obtain ⟨toFun,HtoFun, HtoFun'⟩  :=  HP
    Hint "Apply the similar procedure to construct `invFun` and obtain its property. "
    obtain ⟨invFun, HinvFun, HinvFun'⟩ := HQ
    Hint "Apply beta reduction to all the hypothesis  to simplify the expression by eliminating the lambda abstraction and evaluating function applications directly. More specifically,
    the beta_reduce tactic change (fun x => f x) y to f y.
    Try `beta_reduce at *`. BTW: `simp_all` also dose the job. "
    beta_reduce at *
    Hint "Now we have finished the preparation work. Use `constructor to split the goal"
    refine ⟨?_, ?_, ?_⟩
    Hint "Pick the 2nd goal which constructs equivalence using `pick_goal 2`. "
    · Hint "Apply MulEquiv.intro to construct the equivalence.
        Try `apply MulEquiv.intro toFun invFun`.
      "
      apply MulEquiv.intro toFun invFun
      · Hint "To show invFun ∘ toFun is the identity. One observe that the identity is the unique homomorphism from P to P factors G→*P.
        The idea is to use ExistsUnique.unique claim, but there are many meta-varibles to filling.
        Try `have HPid := (hPu piP hP).unique (y₁:=MonoidHom.id P) (y₂ :=MonoidHom.comp invFun toFun) ?_ ?_ `.
        The last ?_ ?_ tells Lean what we will fill in the gap later.
        "
        have HPid := (hPu piP hP).unique (y₁:=MonoidHom.id P) (y₂ :=MonoidHom.comp invFun toFun) ?_ ?_
        Hint "Use `rw [Function.leftInverse_iff_comp]` to rewrite the goal to `invFun ∘ toFun = id`. "
        rw [Function.leftInverse_iff_comp]
        Hint "This is nothing but {HPid}. But one technique issue have to be dressed: composition of group homomorphism is not simply function composition in Lean. Use `MonoidHom.coe_comp` to rewrite the goal to `⇑(MonoidHom.comp invFun toFun) = id`. "
        rw [<-MonoidHom.coe_comp]
        Hint "Now use {HPid}."
        rw [<-HPid]
        Hint "Now the claim become trivial. Try `trivial` or `rfl`. "
        rfl
        · Hint "This is trivial. Try `rfl`"
          rfl
        · Hint "Use `MonoidHom.coe_comp` to rewrite the goal to
          `(⇑invFun ∘ ⇑toFun) ∘ ⇑piP = ⇑piP`"
          rw [MonoidHom.coe_comp]
          Hint "Function composition is associative, try `rw [Function.comp_assoc]`"
          rw [Function.comp_assoc]
          Hint "Now use {HtoFun} and {HinvFun} to close the goal"
          rw [HtoFun,HinvFun]
      · Hint "The proof of right inverse is similar to the proof of left inverse. We will not give further hints for this point. Enjoy. "
        have HQid :=  (hQu piQ hQ).unique (y₁:=MonoidHom.id Q) (y₂ :=MonoidHom.comp toFun invFun) ?_ ?_
        rw [Function.rightInverse_iff_comp]
        rw [<-MonoidHom.coe_comp,<-HQid]
        ext;simp
        · ext;simp
        · simp_all
          rw [Function.comp_assoc,HinvFun,HtoFun]
      · Hint "The map is multiplicative by definition. Try `exact toFun.map_mul`"
        exact toFun.map_mul
    Hint "You had just finished the construction of the multiplicative equivalence P ≃* Q. Now we need to prove its properties. Try `simp` to make the goal more readable. "
    · simp
      Hint "This is just {HtoFun}."
      rw [HtoFun]
    · Hint "This is more or less {HtoFun'}. But we need to view P≃*Q as P →* Q. First introduce the assumptions, say `intro y hy`. "
      intro y hy
      Hint "Now specialize the hypothesis {HtoFun'} to {y} and {hy}. Try `specialize HtoFun' y hy`."
      specialize HtoFun' y hy
      Hint "Now use try to close the goal use {HtoFun'}. Try `simp`. "
      simp [<-HtoFun']





NewTheorem MonoidHom.coe_comp MonoidHom.id MonoidHom.comp Function.comp_assoc

section
