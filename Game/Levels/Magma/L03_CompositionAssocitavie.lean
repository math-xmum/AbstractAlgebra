import Game.Metadata

import Game.Levels.Lemmas.Group

World "Magma"

Level 3
Title "Composition is associative"

open Set

Introduction "The following statement proves that function composition is associative. That is, for functions $f$, $g$, and $h$, the composition $(f ∘ g) ∘ h$ is equal to $f ∘ (g ∘ h)$."

Statement {α : Type*} (f g h : α → α): (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
  Hint "To prove that two functions are equal, we can show they give the same output for any input. Let's use `ext` to introduce a variable $x$ and prove the functions give the same result when applied to $x$."
  ext x
  Hint "Now we need to show that $((f ∘ g) ∘ h)(x) = (f ∘ (g ∘ h))(x)$. Let's expand the left side using the definition of function composition. We can use `rw [Function.comp_apply]`."
  rw [Function.comp_apply]
  Hint "Now our goal is $(f \\circ g)(h(x)) = (f \\circ (g \\circ h))(x)$. Let's expand $(f \\circ g)(h(x))$ further."
  rw [Function.comp_apply]
  Hint "Our goal is now $f(g(h(x))) = (f \\circ (g \\circ h))(x)$. Let's expand the right side using the definition of function composition."
  rw [Function.comp_apply]
  Hint "Now we have $f(g(h(x))) = f((g \\circ h)(x))$. Let's expand $(g \\circ h)(x)$ to complete the proof."
  rw [Function.comp_apply]


Conclusion "You proved that function composition is associative by showing both sides agree on every input. Associativity is one of the key axioms that makes function composition a semigroup operation."

OnlyTactic ext rw
NewTheorem Function.comp_apply
OnlyTheorem Function.comp_apply
