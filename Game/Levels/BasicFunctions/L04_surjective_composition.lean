import Game.Metadata

World "BasicFunctions"
Level 4
Title "Composition of surjective function."


Introduction "If $f : α → β$ and $g : β → γ$ are both surjective, then $g ∘ f : α → γ$ is also surjective.

The idea: given any $y : γ$, surjectivity of $g$ gives us $x : β$ with $g(x) = y$, and surjectivity of $f$ gives us $a : α$ with $f(a) = x$. Then $(g ∘ f)(a) = g(f(a)) = g(x) = y$."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (g ∘ f) := by
  Hint "The goal asks us to show `∀ y, ∃ a, (g ∘ f) a = y`. Use `intro y` to fix an arbitrary element $y : γ$.

The `intro` tactic moves the leading `∀` binder into the local context as a variable."
  intro y
  Hint "Since $g$ is surjective, `{hg} {y}` has type `∃ x, g x = {y}`. Use `rcases {hg} {y} with ⟨x, hx⟩` to extract the witness `x` and proof `hx : g x = {y}`.

The `rcases` tactic destructs existential statements: `rcases h with ⟨w, hw⟩` gives you the witness and its property."
  rcases hg y with ⟨x, hx⟩
  Hint "Now use surjectivity of $f$ to find a preimage of `{x}`. Use `rcases {hf} {x} with ⟨a, ha⟩` to get `a : α` with `ha : f a = {x}`."
  rcases hf x with ⟨a, ha⟩
  Hint "We claim `{a}` is the preimage we need. Use `use {a}` to set the existential witness.

The `use` tactic provides a witness for an `∃` goal, reducing `∃ x, P x` to `P a`."
  use a
  Hint "The goal is `(g ∘ f) {a} = {y}`, which is `g (f {a}) = {y}`. We know `{ha} : f {a} = {x}` and `{hx} : g {x} = {y}`. Use `rw [← {hx}, ← {ha}]` to rewrite backwards.

The `←` arrow in `rw` rewrites right-to-left: `rw [← h]` replaces the RHS of `h` with its LHS."
  rw [← hx, ← ha]
  Hint "After rewriting, both sides are definitionally equal. Use `rfl` to finish."
  rfl

Conclusion "The composition of surjective functions is surjective. The proof used `rcases` to extract witnesses from existential hypotheses, `use` to provide a witness for the existential goal, and `rw` to chain the equalities together."
-- NewTactic moved to BasicLean
