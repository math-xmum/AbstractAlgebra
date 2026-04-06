import Game.Metadata

World "BasicLean"
Level 4

Title "Containing relation is transitive."


Introduction "This level introduces three new tactics: `intro`, `apply`, and `exact`. You will use them to prove that the subset relation is transitive: if $r \\subseteq s$ and $s \\subseteq t$, then $r \\subseteq t$.

Recall that $r \\subseteq s$ means every element of $r$ is also in $s$. So to prove $r \\subseteq t$, we take an arbitrary element of $r$ and show it belongs to $t$ by chaining the two hypotheses."

Statement subset_trans' {α : Type*} (r s t : Set α): r ⊆ s → s ⊆ t → r ⊆ t := by
  Hint "**`intro`** moves hypotheses from the goal into the local context. When your goal starts with `∀` or `→`, `intro` peels off the outermost binder and gives it a name.

Syntax: `intro h₁ h₂ x hx` introduces four things at once -- the hypothesis `h₁ : r ⊆ s`, the hypothesis `h₂ : s ⊆ t`, an arbitrary element `x`, and the hypothesis `hx : x ∈ r`.

Use `intro h₁ h₂ x hx` to bring all four into context."
  intro h₁ h₂ x hx
  Hint "**`apply`** works backward from the goal. If the goal is `x ∈ t` and you have `{h₂} : s ⊆ t` (which means `∀ x, x ∈ s → x ∈ t`), then `apply {h₂}` changes the goal to `x ∈ s` -- the premise that `{h₂}` needs.

Syntax: `apply {h₂}`."
  apply h₂
  Hint "The goal is now `x ∈ s`. Since `{h₁} : r ⊆ s`, applying `{h₁}` reduces the goal to `x ∈ r`. Use `apply {h₁}`."
  apply h₁
  Hint "**`exact`** closes the goal by providing a term that exactly matches it. The goal is `x ∈ r`, which is precisely `{hx}`.

Syntax: `exact {hx}`."
  exact hx


Conclusion "Well done! You have learned three essential tactics:
- **`intro`** moves universally quantified variables and implication hypotheses from the goal into the context.
- **`apply`** works backward: given a hypothesis `h : A → B` and a goal `B`, it reduces the goal to `A`.
- **`exact`** closes the goal by supplying a term that matches it exactly.

Together, these three tactics let you reason forward (introducing assumptions) and backward (reducing goals to simpler ones)."

NewTactic intro apply exact
