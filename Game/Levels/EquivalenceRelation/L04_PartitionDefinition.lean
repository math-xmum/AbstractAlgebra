import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

theorem Set.ne_empty_of_mem {a : α} {s : Set α} (h : a ∈ s) : s ≠ ∅ := fun e =>
  absurd (e ▸ h) (Set.mem_empty_iff_false a).mp


World "EquivalenceRelation"

Level 4

variable {α : Type*} (C : Set (Set α))


Introduction "The following statement shows the equivalence between two definitions of a partition of a set. The first definition (IsPartition) states that a collection $C$ of subsets is a partition if it doesn't contain the empty set and every element belongs to exactly one subset in $C$. The second definition (IsPartition') states that $C$ doesn't contain the empty set, covers the whole space, and its elements are pairwise disjoint."

Statement : IsPartition C ↔ IsPartition' C := by
  Hint "We start by unfolding the definition of IsPartition. This will reveal that it consists of two parts: ∅ ∉ C and a uniqueness condition for elements. You can use `unfold`."
  unfold IsPartition
  Hint "Now we unfold IsPartition' to see its three components: $∅ ∉ C$, the union covers the whole space, and pairwise disjointness. Again, use `unfold`."
  unfold IsPartition'
  Hint "The goal now has similar structures on both sides. We can use `and_congr_right'` to focus on the parts that differ, since both definitions share the $∅ ∉ C$ condition."
  apply and_congr_right'
  Hint "We now need to prove the equivalence between the uniqueness condition and the union+disjointness conditions. We'll split this into two implications using `constructor`."
  constructor
  Hint "For the forward implication (→), we introduce the hypothesis H2 that every element has a unique containing set in $C$. Use `rintro`."
  rintro H2
  Hint "We need to prove two things: that the union covers the whole space, and the pairwise disjointness. We'll tackle them separately using `constructor`."
  constructor
  Hint "To show $⋃₀ C = Set.univ$, we can rewrite it using set extensionality to show every element is in the union. Use `rw [Set.eq_univ_iff_forall]`."
  rw [Set.eq_univ_iff_forall]
  Hint "We need to show for an arbitrary element x that it's in some set in $C$. We can use the uniqueness hypothesis H2 to find this set. Use `intro x`."
  intro x
  Hint "The set membership can be rewritten using the definition of union. Use `rw [Set.mem_sUnion]`."
  rw [Set.mem_sUnion]
  Hint "From {H2} {x}, we can obtain the unique set t containing {x}. Use `obtain ⟨t, _, _⟩ := {H2} {x}`."
  obtain ⟨t, _, _⟩ := H2 x
  Hint "We can now use this set {t} as witness for the existential. Use `use t`."
  use t
  Hint "For the second part of the forward implication, we need to show pairwise disjointness. We introduce sets `a` and `b` in $C$ that intersect. Use `intro a ha b hb hab`."
  intro a ha b hb hab
  Hint "The intersection non-emptiness can be rewritten as having a common element. Use `push_neg at hab`."
  push_neg at hab
  Hint "We can obtain the common element `x` from the non-empty intersection. Use `obtain ⟨x,hax,hbx⟩ := hab`."
  obtain ⟨x,hax,hbx⟩ := hab
  Hint "We specialize our uniqueness hypothesis {H2} to this element {x}. Use `specialize {H2} {x}`."
  specialize H2 x
  Hint "We unfold the ExistsUnique to work with its components. Use `unfold ExistsUnique at {H2}`."
  unfold ExistsUnique at H2
  Hint "We can obtain the unique set `c` containing {x} from {H2}. Use `obtain ⟨c, hc1, hc2⟩ := {H2}`."
  obtain ⟨c, hc1, hc2⟩ := H2
  Hint "Using the uniqueness, we can show both {a} and {b} must equal {c}. Use `have aeqc := {hc2} {a} ⟨{ha},{hax}⟩`."
  have aeqc := hc2 a ⟨ha,hax⟩
  Hint "Similarly, {b} must equal {c}. Use `have beqc := {hc2} {b} ⟨{hb},{hbx}⟩`."
  have beqc := hc2 b ⟨hb,hbx⟩
  Hint "Now we can rewrite using these equalities to conclude. Use `rw [aeqc, beqc]`."
  rw [aeqc, beqc]
  Hint "For the reverse implication (←), we introduce the hypotheses about union and disjointness. Use `rintro ⟨H1,H2⟩`."
  rintro ⟨H1,H2⟩
  Hint "We rewrite the union equality using extensionality. Use `rw [Set.eq_univ_iff_forall] at {H1}`."
  rw [Set.eq_univ_iff_forall] at H1
  Hint "For an arbitrary element `x`, we need to show there's a unique set in $C$ containing it. Use `intro x`."
  intro x
  Hint "From the covering property {H1}, we can obtain some set `b` containing {x}. Use `obtain ⟨b, hb⟩ := {H1} {x}`."
  obtain ⟨b, hb⟩ := H1 x
  Hint "We'll use {b} as our candidate for the unique set. Use `use b`."
  use b
  Hint "We need to show both existence and uniqueness. We'll structure this with `constructor`."
  constructor
  Hint "The existence part follows directly from how we chose {b}. Use `exact hb`."
  exact hb
  Hint "For uniqueness, we introduce another set `c` containing {x}. Use `intro c hc`."
  intro c hc
  Hint "We show {c} and {b} intersect at {x}, so they must be equal by {H2}. Use `have hcb: c ∩ b ≠ ∅ := ...`."
  have hcb: c ∩ b ≠ ∅ := Set.ne_empty_of_mem (a :=x) ⟨hc.2,hb.2⟩
  Hint "Finally, we apply the disjointness condition to conclude. Use `exact {H2} {c} {hc}.1 {b} {hb}.1 hcb`."
  exact H2 c hc.1 b hb.1 hcb


OnlyTactic intro rfl rw exact simp «have» refine obtain specialize
