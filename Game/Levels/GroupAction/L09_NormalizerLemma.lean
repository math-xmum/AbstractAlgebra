import Game.Metadata
import Mathlib.Algebra.Group.Subgroup.Basic

World "GroupAction"

Level 9

Title "The Normalizer Lemma"

Introduction "
A subgroup H of G is **normal** if gHg⁻¹ = H for every g ∈ G.
Equivalently, H is normal in G if and only if every element of G
normalizes H, i.e., N_G(H) = G.

In Mathlib, `H.Normal` is the typeclass for normality, and
the characterization is:
  H.normalizer = ⊤ ↔ H.Normal  (`Subgroup.normalizer_eq_top_iff`).

Your goal: show that if H is normal in G, then H.normalizer = ⊤.
This captures the idea that the normalizer of a normal subgroup is
the entire group.
"

variable {G : Type*} [Group G] (H : Subgroup G)

/-- Helper: a normal subgroup's normalizer contains every element. -/
private lemma normalizer_eq_top_of_normal [H.Normal] (g : G) :
    g ∈ H.normalizer := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact Subgroup.Normal.conj_mem ‹H.Normal› h hh g
  · intro hh
    have : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rw [← this]
    exact Subgroup.Normal.conj_mem' ‹H.Normal› _ hh g

Statement [H.Normal] : H.normalizer = ⊤ := by
  Hint "We need to show that the normalizer equals the top subgroup ⊤ (all of G).
  Use `ext g` to show every element g is in H.normalizer."
  ext g
  Hint "The right-hand side `g ∈ ⊤` is always true. Use `simp` to simplify it,
  leaving us to show `g ∈ H.normalizer`."
  simp only [Subgroup.mem_top, iff_true]
  Hint "Now unfold the normalizer membership using
  `rw [Subgroup.mem_normalizer_iff]`."
  rw [Subgroup.mem_normalizer_iff]
  Hint "Introduce h and split with `intro h` then `constructor`."
  intro h
  constructor
  · Hint "Use the normality hypothesis: `Subgroup.Normal.conj_mem` says that
    if h ∈ H and H is normal, then g * h * g⁻¹ ∈ H."
    intro hh
    exact Subgroup.Normal.conj_mem ‹H.Normal› h hh g
  · Hint "For the reverse, conjugate by g⁻¹. Since H is normal,
    `Subgroup.Normal.conj_mem'` gives g⁻¹ * n * g ∈ H.
    Use the fact that h = g⁻¹ * (g * h * g⁻¹) * g."
    intro hh
    have key : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rw [← key]
    exact Subgroup.Normal.conj_mem' ‹H.Normal› _ hh g

Conclusion "
Excellent! You have shown that a normal subgroup's normalizer is the whole group.
In Mathlib, this is `Subgroup.normalizer_eq_top`.
Combined with Level 8, we see:
  H ≤ H.normalizer ≤ ⊤,
and H is normal iff H.normalizer = ⊤. The normalizer is the largest subgroup
in which H sits normally.
"

NewTheorem Subgroup.normalizer_eq_top Subgroup.normalizer_eq_top_iff Subgroup.Normal.conj_mem Subgroup.mem_top
NewTactic ext simp group rw constructor intro exact
