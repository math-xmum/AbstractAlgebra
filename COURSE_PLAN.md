# Abstract Algebra Game — Course Plan

## Reference Book
**Fraleigh, "A First Course in Abstract Algebra"**
- Located at: `reference/Fraleigh, A first course in abstract algebra.pdf`

## Course Goal
Emphasize **group actions** as a central tool, then use group actions to prove **Sylow theorems**.
Following Fraleigh's approach (Sections 36-37).

## Fraleigh's Proof Route for Sylow Theorems

### Prerequisites (Fraleigh Section 16-17)
- Group action on a set (G-set)
- Orbits and stabilizers
- Burnside's formula / orbit counting

### Key Theorem (Fraleigh 36.1): Fixed Point Counting for p-groups
If G is a p-group acting on a finite set X, then:
  |X| ≡ |X^G| (mod p)
where X^G = {x ∈ X | gx = x for all g ∈ G} is the set of fixed points.

This is THE key tool for all three Sylow theorems.

### Cauchy's Theorem (Fraleigh 36.3)
If p divides |G|, then G has an element of order p.
- Proof: Let X = {(g1,...,gp) | g1*g2*...*gp = e}, cyclic group ⟨σ⟩ of order p acts on X
- |X| = |G|^(p-1), so p | |X|
- |X^⟨σ⟩| ≡ |X| (mod p), and (e,e,...,e) ∈ X^⟨σ⟩, so |X^⟨σ⟩| ≥ p
- Any non-identity fixed point gives an element of order p

### Normalizer Lemma (Fraleigh 36.6)
If H is a p-subgroup of G, then:
  (N[H] : H) ≡ (G : H) (mod p)
- Proof: H acts on left cosets of H in G by left translation
- Fixed cosets are exactly those in N[H]

### First Sylow Theorem (Fraleigh 36.8)
|G| = p^n * m where p ∤ m. Then:
1. G contains a subgroup of order p^i for each 1 ≤ i ≤ n
2. Each such subgroup is normal in a subgroup of order p^(i+1)
- Proof: Induction using Normalizer Lemma + Cauchy's theorem on N[H]/H

### Second Sylow Theorem (Fraleigh 36.10)
Any two Sylow p-subgroups are conjugate.
- Proof: P2 acts on left cosets of P1, use fixed point counting

### Third Sylow Theorem (Fraleigh 36.11)
Number of Sylow p-subgroups ≡ 1 (mod p) and divides |G|.
- Proof: P acts on set S of all Sylow p-subgroups by conjugation
- S^P = {P} (only fixed point), so |S| ≡ 1 (mod p)
- G acts on S by conjugation, single orbit, so |S| = (G : N[P]) divides |G|

### Applications (Fraleigh Section 37)
- Class equation: |G| = |Z(G)| + Σ [G : C_G(g_i)]
- p-groups are solvable
- Groups of order p² are abelian
- Simple group classification for small orders

---

## Proposed Game Structure

### Existing Worlds (with status)

#### 1. BasicLean (10 levels) — GOOD ✓
No changes needed. Well-documented.

#### 2. BasicFunctions (6 levels) — MOSTLY GOOD
- TODO: Add Introduction to L03_surjective_definition

#### 3. EquivalenceRelation (22 levels) — NEEDS MAJOR REWORK
**Problem**: 22 levels is too many. Levels L07-L22 are poorly documented.
**Plan**:
- Keep L01-L06 (equivalence relations, partitions) — add documentation
- Merge/simplify L07-L22 (equivalence classes, quotient construction) into ~6 levels
- Add Introduction, Hints, and Conclusion to every level
- Target: ~12 levels total

#### 4. Magma (9 levels) — OK
- TODO: Add more hints to L05, L06

#### 5. BasicGroupTheory (18 levels) — SPLIT INTO TWO
**Plan**: Split into:
- **GroupBasics** (L01-L10): group axioms, inverses, subgroups, commutators
  - Fix L06 (IsSubgroup — confusing intro)
  - Fix L07 (kZ — has sorry)
  - Fix L08 (Zn — incomplete hints)
- **CosetsAndLagrange** (L11-L18): cosets, Lagrange theorem
  - Well-documented, minor fixes

#### 6. GroupHomo (6 levels) — GOOD ✓
Covers: homomorphism properties, kernel, normal subgroups, universal property.

#### 7. GroupAction (3 levels) — EXPAND SIGNIFICANTLY
Currently only: orbit equality, conjugation stabilizer, orbit-stabilizer.
**Expand to ~10 levels** (see below).

### New Worlds

#### 8. GroupAction (expanded) — ~10 levels
Following Fraleigh Sections 16-17, 36:

| Level | Topic | Fraleigh |
|-------|-------|----------|
| L01 | Group action definition, examples | §16 |
| L02 | Orbits and orbit equality | §16 (existing) |
| L03 | Stabilizer and its properties | §16 |
| L04 | Orbit-Stabilizer theorem | §16.16 (existing) |
| L05 | Conjugation action | §16 (existing L02) |
| L06 | Action on cosets | new |
| L07 | Fixed point counting for p-groups: \|X\| ≡ \|X^G\| (mod p) | §36.1 |
| L08 | Cauchy's theorem via group action | §36.3 |
| L09 | Normalizer and its properties | §36.5-36.6 |
| L10 | Class equation | §37.2 |

#### 9. Sylow (new) — ~8 levels

| Level | Topic | Fraleigh |
|-------|-------|----------|
| L01 | p-subgroups and Sylow p-subgroups (definitions) | §36.4, 36.9 |
| L02 | Normalizer lemma: (N[H]:H) ≡ (G:H) (mod p) | §36.6 |
| L03 | First Sylow Theorem (existence) | §36.8 |
| L04 | Second Sylow Theorem (conjugacy) | §36.10 |
| L05 | Third Sylow Theorem (counting) | §36.11 |
| L06 | Application: groups of order p² are abelian | §37.6 |
| L07 | Application: determine groups of small order | §37 |
| L08 | Application: no simple group of order 12/... | §37 |

### World Dependency Graph

```
BasicLean
  ├→ BasicFunctions
  │     └→ EquivalenceRelation (~12 levels)
  │
  └→ Magma
        └→ GroupBasics (~10 levels)
              ├→ CosetsAndLagrange (~8 levels)
              │     └→ GroupHomo (6 levels)
              │           └→ GroupAction (~10 levels)
              │                 └→ Sylow (~8 levels)
              │
              └→ (direct to GroupAction if cosets covered there)
```

---

## Documentation Standards (for all levels)

Every level MUST have:
1. **Introduction**: 2-5 sentences explaining the mathematical concept in plain language
2. **Statement**: clear theorem/definition with proper types
3. **Hints**: step-by-step guidance for each proof step (use `Hint` and `Hint (hidden := true)`)
4. **Conclusion**: 1-2 sentences summarizing what was proved and why it matters
5. **NewTheorem/NewTactic**: with `TheoremDoc`/`TacticDoc` documentation

Use BasicLean levels as the documentation quality template.

---

## Implementation Priority

### Phase 1: Fix existing content
1. Add documentation to all poorly-documented EquivalenceRelation levels
2. Fix BasicGroupTheory L06, L07, L08
3. Add missing Introductions/Conclusions everywhere

### Phase 2: Restructure
1. Split BasicGroupTheory into GroupBasics + CosetsAndLagrange
2. Simplify EquivalenceRelation from 22 to ~12 levels

### Phase 3: Expand GroupAction
1. Add levels L06-L10 (action on cosets, fixed points, Cauchy, normalizer, class equation)

### Phase 4: Add Sylow world
1. Implement all 8 Sylow levels following Fraleigh's proofs

### Phase 5: Polish
1. Review all levels for consistency
2. Playtest all levels end-to-end
3. Check mathlib API usage is clean
