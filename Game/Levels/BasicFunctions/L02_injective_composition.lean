import Game.Metadata

World "BasicFunctions"
Level 2
Title "Composition of injective function."

Introduction "If $f : α → β$ and $g : β → γ$ are both injective, then $g ∘ f : α → γ$ is also injective.

The key idea: if $g(f(x)) = g(f(y))$, then injectivity of $g$ gives $f(x) = f(y)$, and injectivity of $f$ gives $x = y$. We peel off the outer function first, then the inner one."
Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (g ∘ f) := by
  Hint (hidden := true) "The goal is `Function.Injective (g ∘ f)`. To see what this means concretely, use `unfold Function.Injective at *` — this replaces `Function.Injective` with its definition in both the goal and all hypotheses.

The `unfold` tactic expands a definition name in place. Adding `at *` applies it everywhere."
  unfold Function.Injective at *
  Hint (hidden := true) "The goal is now `∀ (x y : α), (g ∘ f) x = (g ∘ f) y → x = y`. Use `intro x y h` to introduce two arbitrary elements and the hypothesis that $g(f(x)) = g(f(y))$.

The `intro` tactic moves universally quantified variables and implication antecedents from the goal into the local context."
  intro x y h
  Hint (hidden := true) "Our goal is `{x} = {y}`. The hypothesis `{hf}` says `∀ a b, f a = f b → a = b`. So `apply {hf}` changes the goal to `f {x} = f {y}`.

The `apply` tactic works backwards: if `{hf}` proves `P → Q` and the goal is `Q`, then `apply {hf}` changes the goal to `P`."
  apply hf
  Hint (hidden := true) "Now the goal is `f {x} = f {y}`. The hypothesis `{hg}` says `∀ a b, g a = g b → a = b`, but used via `apply` it changes the goal to `g (f {x}) = g (f {y})`.

Use `apply {hg}` to reduce the goal to showing the equality under $g$."
  apply hg
  Hint (hidden := true) "The goal `g (f {x}) = g (f {y})` is exactly our hypothesis `{h}`. Use `exact {h}` to close the goal.

The `exact` tactic closes a goal by providing a term that has exactly the required type."
  exact h


-- NewTactic moved to BasicLean
OnlyTactic apply intro exact rw unfold
Conclusion "The composition of injective functions is injective. Notice the proof strategy: we used `apply` twice to peel back the functions layer by layer, reducing $g(f(x)) = g(f(y))$ first to $f(x) = f(y)$, then to $x = y$."
