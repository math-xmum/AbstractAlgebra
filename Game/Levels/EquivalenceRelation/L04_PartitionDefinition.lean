import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

theorem Set.ne_empty_of_mem {a : α} {s : Set α} (h : a ∈ s) : s ≠ ∅ := fun e =>
   ((Set.mem_empty_iff_false a).mp (e ▸ h))


World "EquivalenceRelation"

Level 4

variable {α : Type*} (C : Set (Set α))


Introduction "
A **partition** of a set divides it into non-overlapping, exhaustive pieces. There are two natural ways to state this:

- **IsPartition C**: The collection $C$ does not contain $\\emptyset$, and every element belongs to **exactly one** member of $C$ (existence + uniqueness, written `∃!`).
- **IsPartition' C**: The collection $C$ does not contain $\\emptyset$, the union $\\bigcup C$ equals the whole space, and distinct members of $C$ are **disjoint**.

These two formulations are equivalent. In the forward direction, uniqueness gives both coverage and disjointness. In the reverse direction, coverage plus disjointness gives uniqueness.

This is a longer proof. Key new tactics you will use:

- `unfold <name>` -- expands a definition in the goal.
- `apply <lemma>` -- works backwards from the goal, matching its conclusion.
- `obtain ⟨x, hx⟩ := H` -- destructs an existential hypothesis.
- `specialize H x` -- substitutes a specific value into a universally quantified hypothesis.
- `push_neg` -- pushes negations inward through quantifiers.
- `use t` -- provides a witness for an existential goal.
"

Statement : IsPartition C ↔ IsPartition' C := by
  Hint "Start by expanding the definition of `IsPartition` with `unfold IsPartition`. The `unfold` tactic replaces a defined name in the goal with its definition."
  unfold IsPartition
  Hint "Now expand `IsPartition'` with `unfold IsPartition'`."
  unfold IsPartition'
  Hint "Both sides share the condition `∅ ∉ C`. Use `apply and_congr_right'` to keep that part and focus on proving the remaining parts are equivalent.

The `apply` tactic works backwards: if the goal matches the conclusion of a lemma, it replaces the goal with the lemma's premises."
  apply and_congr_right'
  Hint "We need an iff between the uniqueness condition and the (coverage + disjointness) condition. Use `constructor` to split into two implications."
  constructor
  Hint "**Forward direction.** Assume every element has a unique containing set. Use `rintro H2` to introduce this hypothesis.

The `rintro` tactic is like `intro` but supports pattern-matching on the introduced term."
  rintro H2
  Hint "We must show two things (coverage and disjointness). Use `constructor` to split the conjunction."
  constructor
  Hint "**Coverage:** We need the union of `C` to equal the universal set. Rewrite this as a forall statement with `rw [Set.eq_univ_iff_forall]`."
  rw [Set.eq_univ_iff_forall]
  Hint "Introduce an arbitrary element `x` with `intro x`."
  intro x
  Hint "Rewrite membership in a union: `rw [Set.mem_sUnion]` turns the goal into `∃ t ∈ C, x ∈ t`."
  rw [Set.mem_sUnion]
  Hint "From the uniqueness hypothesis `{H2} x`, we can extract the unique set containing `x`. Use `obtain ⟨t, _, _⟩ := {H2} x`.

The `obtain` tactic destructs an existential or conjunction into its components."
  obtain ⟨t, _, _⟩ := H2 x
  Hint "Provide the witness `t` for the existential with `use t`.

The `use` tactic supplies a witness for an existential goal `∃ x, P x`."
  use t
  Hint "**Disjointness:** We must show that if two sets in $C$ have non-empty intersection, they are equal. Use `intro a ha b hb hab`."
  intro a ha b hb hab
  Hint "The hypothesis `hab` says the intersection is non-empty. Use `push_neg at hab` to rewrite it as the existence of a common element.

The `push_neg` tactic pushes negations inward: `¬ (S = ∅)` becomes `∃ x ∈ S, True` (or similar)."
  push_neg at hab
  Hint "Extract the common element `x` with `obtain ⟨x, hax, hbx⟩ := hab`."
  obtain ⟨x,hax,hbx⟩ := hab
  Hint "Specialize the uniqueness hypothesis to this element: `specialize {H2} x`.

The `specialize` tactic applies a hypothesis to specific arguments, replacing it with the result."
  specialize H2 x
  Hint "Unfold the `ExistsUnique` to access its components: `unfold ExistsUnique at {H2}`."
  unfold ExistsUnique at H2
  Hint "Extract the unique set `c` and the uniqueness proof: `obtain ⟨c, hc1, hc2⟩ := {H2}`."
  obtain ⟨c, hc1, hc2⟩ := H2
  Hint "Since `a` is in $C$ and contains `x`, the uniqueness condition forces `a = c`. Use `have aeqc := {hc2} a ⟨ha, hax⟩`."
  have aeqc := hc2 a ⟨ha,hax⟩
  Hint "Similarly, `b = c`. Use `have beqc := {hc2} b ⟨hb, hbx⟩`."
  have beqc := hc2 b ⟨hb,hbx⟩
  Hint "Now rewrite `a` and `b` to `c` with `rw [aeqc, beqc]`."
  rw [aeqc, beqc]
  Hint "**Reverse direction.** Assume coverage and disjointness. Use `rintro ⟨H1, H2⟩` to destructure the conjunction."
  rintro ⟨H1,H2⟩
  Hint "Rewrite the coverage hypothesis: `rw [Set.eq_univ_iff_forall] at {H1}` turns it into a forall."
  rw [Set.eq_univ_iff_forall] at H1
  Hint "Introduce an arbitrary element with `intro x`."
  intro x
  Hint "From coverage, get a set containing `x`: `obtain ⟨b, hb⟩ := {H1} x`."
  obtain ⟨b, hb⟩ := H1 x
  Hint "Provide `b` as the witness for the unique set: `use b`."
  use b
  Hint "Split existence and uniqueness with `constructor`."
  constructor
  Hint "Existence follows directly: `exact hb`."
  exact hb
  Hint "For uniqueness, introduce another set `c` containing `x`: `intro c hc`."
  intro c hc
  Hint "The sets `c` and `b` both contain `x`, so their intersection is non-empty. Use `have hcb : c ∩ b ≠ ∅ := Set.ne_empty_of_mem (a := x) ⟨hc.2, hb.2⟩`."
  have hcb: c ∩ b ≠ ∅ := Set.ne_empty_of_mem (a :=x) ⟨hc.2,hb.2⟩
  Hint "By disjointness, `c = b`. Use `exact {H2} c hc.1 b hb.1 hcb`."
  exact H2 c hc.1 b hb.1 hcb


OnlyTactic intro rfl rw exact simp «have» refine obtain specialize
