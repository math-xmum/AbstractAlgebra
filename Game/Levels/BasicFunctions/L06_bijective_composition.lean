import Game.Metadata

World "BasicFunctions"
Level 6
Title "Composition of surjective function."

Introduction "If $f : α → β$ and $g : β → γ$ are both bijective, then $g ∘ f : α → γ$ is also bijective. Since bijectivity means being both injective and surjective, we split the proof into two parts and reuse the ideas from Levels 2 and 4.

Note: if `hf : Function.Bijective f`, then `hf.1` is the injectivity part and `hf.2` is the surjectivity part (since `Bijective` is defined as a conjunction `∧`)."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (g ∘ f) := by
  Hint "The goal is `Function.Bijective (g ∘ f)`, which is `Function.Injective (g ∘ f) ∧ Function.Surjective (g ∘ f)`. Use `constructor` to split it into two subgoals.

The `constructor` tactic splits a goal of the form `P ∧ Q` into two separate goals: first `P`, then `Q`."
  constructor
  Hint "**Subgoal 1: Injectivity.** We must show `∀ x y, (g ∘ f) x = (g ∘ f) y → x = y`. Use `intro x y h` to introduce the variables and hypothesis."
  intro x y h
  Hint "The goal is `{x} = {y}`. Since `{hf}.1` is the injectivity of $f$, `apply {hf}.1` changes the goal to `f {x} = f {y}`.

Recall: `.1` extracts the first component of a conjunction. Here `{hf} : Bijective f` is `Injective f ∧ Surjective f`, so `{hf}.1 : Injective f`."
  apply hf.1
  Hint "The goal is `f {x} = f {y}`. Use `apply {hg}.1` — the injectivity of $g$ — to reduce this to `g (f {x}) = g (f {y})`."
  apply hg.1
  Hint "The goal `g (f {x}) = g (f {y})` matches `{h}` exactly. Use `exact {h}`."
  exact h
  Hint "**Subgoal 2: Surjectivity.** We must show `∀ y, ∃ a, (g ∘ f) a = y`. Use `intro y` to fix an arbitrary element of $γ$."
  intro y
  Hint "Use surjectivity of $g$ to find a preimage: `rcases {hg}.2 {y} with ⟨x, hx⟩` gives `x : β` and `hx : g x = {y}`.

Here `{hg}.2` is the surjectivity part of `{hg} : Bijective g`."
  rcases hg.2 y with ⟨x, hx⟩
  Hint "Now use surjectivity of $f$: `rcases {hf}.2 {x} with ⟨a, ha⟩` gives `a : α` and `ha : f a = {x}`."
  rcases hf.2 x with ⟨a, ha⟩
  Hint "Provide `{a}` as the witness with `use {a}`. The goal becomes `(g ∘ f) {a} = {y}`."
  use a
  Hint "Rewrite using `{ha}` and `{hx}`: `rw [← {hx}, ← {ha}]` transforms the goal so both sides match definitionally."
  rw [← hx, ← ha]
  Hint "Both sides are now definitionally equal. Use `rfl`."
  rfl


Conclusion "The composition of bijective functions is bijective. This proof combined the techniques from the injectivity and surjectivity composition proofs, using `.1` and `.2` to access the two components of the bijectivity hypotheses."
-- NewTactic moved to BasicLean
