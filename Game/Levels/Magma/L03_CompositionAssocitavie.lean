import Game.Metadata

import Game.Levels.Lemmas.Group

World "Magma"

Level 3

open Set

Introduction "
Associativity is a key property that distinguishes a **semigroup** from a mere magma.
Here we prove that the set of functions $\\alpha \\to \\alpha$, under the binary operation of
**function composition** ($\\circ$), is associative:
for functions $f, g, h : \\alpha \\to \\alpha$, we have $(f \\circ g) \\circ h = f \\circ (g \\circ h)$.

To prove two functions are equal in Lean, we use the `ext` tactic (function extensionality),
which reduces the goal to showing they agree on every input. Then we unfold compositions
step by step using `Function.comp_apply`, which says $(f \\circ g)(x) = f(g(x))$.
"

Statement {α : Type*} (f g h : α → α): (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
  Hint "To prove two functions are equal, use `ext x`. This introduces an arbitrary input `x` and changes the goal to showing both sides produce the same output at `x`."
  ext x
  Hint "The goal is `((f ∘ g) ∘ h) x = (f ∘ (g ∘ h)) x`. The theorem `Function.comp_apply` states `(f ∘ g) x = f (g x)`. Use `rw [Function.comp_apply]` to expand the outermost composition on the left."
  rw [Function.comp_apply]
  Hint "Use `rw [Function.comp_apply]` again to expand the remaining `(f ∘ g)` application on the left."
  rw [Function.comp_apply]
  Hint "Now the left side is fully expanded to `f (g (h x))`. Use `rw [Function.comp_apply]` to start expanding the right side."
  rw [Function.comp_apply]
  Hint "One more `rw [Function.comp_apply]` expands the inner composition `(g ∘ h) x` to `g (h x)`, making both sides identical and closing the goal."
  rw [Function.comp_apply]


OnlyTactic ext rw
NewTheorem Function.comp_apply
OnlyTheorem Function.comp_apply
