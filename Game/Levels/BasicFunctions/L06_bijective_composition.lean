import Game.Metadata

World "BasicFunctions"
Level 6
Title "Composition of surjective function."

/-- Composition of injective functions is injective. -/
private lemma injective_comp {α β γ : Type} (f : α → β) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) :=
  fun _ _ h => hf (hg h)

/-- Composition of surjective functions is surjective. -/
private lemma surjective_comp {α β γ : Type} (f : α → β) (g : β → γ)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) := by
  intro y
  rcases hg y with ⟨x, hx⟩
  rcases hf x with ⟨a, ha⟩
  exact ⟨a, by simp [Function.comp, ha, hx]⟩

Introduction "The following statement claims that the composition of two bijective functions is also bijective. Specifically, if $f: α → β$ and $g: β → γ$ are both bijective, then $g ∘ f: α → γ$ is also bijective. A bijective function is both injective (one-to-one) and surjective (onto)."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (g ∘ f) := by
  Hint "To prove that $g ∘ f$ is bijective, we need to show it is both injective and surjective. You can use `constructor` to split the goal into these two parts."
  constructor
  Hint "For injectivity, we chain the injectivity of {f} and {g}. Use `exact injective_comp f g {hf}.1 {hg}.1`."
  exact injective_comp f g hf.1 hg.1
  Hint "For surjectivity, we chain the surjectivity of {f} and {g}. Use `exact surjective_comp f g {hf}.2 {hg}.2`."
  exact surjective_comp f g hf.2 hg.2


Conclusion "Level Completed!"
NewTactic intro apply exact use rw rfl
