# Abstract Algebra Game — Course Plan

## Reference
- **Textbook**: Fraleigh, "A First Course in Abstract Algebra" (`reference/Fraleigh, A first course in abstract algebra.pdf`)
- **Lecture PPTs**: `reference/ppts/01-04` (MAT205 Abstract Algebra II, Ma Jia-Jun)

## Course Structure (from PPTs)

MAT205 Abstract Algebra II has 4 group theory lectures:
1. **Review of Basics** (PPT 01): groups, subgroups, cosets, Lagrange, homomorphisms, normal subgroups, simple groups, quotient groups, isomorphism theorems, Burnside's lemma
2. **Subnormal series** (PPT 02): semi-direct products, composition factors, solvable groups, central series, nilpotent groups, derived series
3. **Sylow Theorem** (PPT 03): McKay's proof of Cauchy, Sylow I/II/III, conjugacy class equation
4. **Sylow Applications** (PPT 04): classifying groups of small order

## Game Scope

The game covers **PPT 01 + 03 + 04** (Review → Group Actions → Sylow).
**PPT 02 (Subnormal series)** is left for classroom lectures — it is hard to formalize in Lean with good pedagogical value, and Sylow theorems do not depend on it.

Core pedagogical path:
```
群基础 → 同态/商群 → 群作用 → Sylow 定理 → 应用
```

---

## Game Worlds

### World 1: BasicLean (10 levels) — DONE
Lean tactic basics: rfl, rw, subset, intersection, union.
No changes needed.

### World 2: BasicFunctions (6 levels) — DONE
Injective, surjective, bijective functions and their compositions.
- TODO: Add Introduction to L03

### World 3: EquivalenceRelation (~12 levels) — NEEDS REWORK
Equivalence relations, partitions, equivalence classes, quotient construction.
- Current: 22 levels, L07-L22 poorly documented
- Plan: Merge/simplify L07-L22 into ~6 levels, add documentation to all

### World 4: Magma (9 levels) — DONE
Magma definition, closure, associativity, homomorphism, identity, isomorphism.
- TODO: Add more hints to L05, L06

### World 5: GroupBasics (~10 levels) — REFACTOR from BasicGroupTheory L01-L10
*Fraleigh Ch.1, PPT 01 slides 1-6*

| Level | Topic | PPT/Fraleigh |
|-------|-------|-------------|
| L01 | Group axioms: associativity | §2 |
| L02 | Semigroup definition | §2 |
| L03 | Left inverse implies right inverse | §4 |
| L04 | Inverse properties | §4 |
| L05 | Uniqueness of inverse | §4 |
| L06 | Subgroup criterion | §5, PPT01 slide 5 |
| L07 | Example: kZ is a subgroup of Z | §6 |
| L08 | Example: Z/nZ as commutative group | §6 |
| L09 | Commutator subgroup | §15 |
| L10 | Elementary 2-group | §11 |

### World 6: CosetsAndLagrange (~8 levels) — REFACTOR from BasicGroupTheory L11-L18
*Fraleigh Ch.2 §10, PPT 01 slides 7-8*

| Level | Topic | PPT/Fraleigh |
|-------|-------|-------------|
| L01 | Coset membership criterion | §10 |
| L02 | Coset as translation of subgroup | §10 |
| L03 | Coset equality criterion | §10 |
| L04 | Cosets are orbits (transitivity) | §10 |
| L05 | Cosets are disjoint | §10 |
| L06 | Klein four-group is not cyclic | §11 |
| L07 | Coset cardinality = subgroup order | §10 |
| L08 | Index and Lagrange's theorem | §10 |

### World 7: GroupHomo (6 levels) — DONE
*Fraleigh Ch.3 §13-15, PPT 01 slides 9-17*

| Level | Topic | PPT/Fraleigh |
|-------|-------|-------------|
| L01 | Homomorphism maps identity to identity | §13 |
| L02 | Homomorphism maps inverse to inverse | §13 |
| L03 | Kernel is a normal subgroup | §14 |
| L04 | Normal subgroup ↔ coset multiplication well-defined | §14, PPT01 slide 10 |
| L05 | Universal property of quotient (existence) | §14, PPT01 slide 16 |
| L06 | Universal property of quotient (uniqueness) | §14, PPT01 slide 16 |

### World 8: GroupAction (~10 levels) — EXPAND from current 3 levels
*Fraleigh §16-17, §36.1-36.6, PPT 03*

This is the **central world** of the course. Group actions are the key tool for Sylow.

| Level | Topic | Fraleigh | PPT |
|-------|-------|----------|-----|
| L01 | Group action definition and examples | §16 | 03 slide 2-3 |
| L02 | Orbits: orbit equality ↔ same orbit | §16 | |
| L03 | Stabilizer properties | §16 | |
| L04 | Orbit-Stabilizer theorem: \|Gx\| = [G : G_x] | §16.16 | |
| L05 | Conjugation action, conjugacy classes | §16 | 03 slide 41 |
| L06 | Action on cosets (G acts on G/H) | §16 | |
| L07 | **Fixed point counting**: \|X\| ≡ \|X^G\| (mod p) for p-groups | §36.1 | 03 slide 10 |
| L08 | **Cauchy's theorem** via group action (McKay's proof) | §36.3 | 03 slide 10-17 |
| L09 | Normalizer N[H] and its properties | §36.5 | |
| L10 | **Normalizer lemma**: (N[H]:H) ≡ (G:H) (mod p) | §36.6 | 03 slide 18 |

### World 9: Sylow (~8 levels) — NEW
*Fraleigh §36.8-36.11, §37, PPT 03-04*

| Level | Topic | Fraleigh | PPT |
|-------|-------|----------|-----|
| L01 | p-subgroups and Sylow p-subgroups (definitions) | §36.4, 36.9 | 03 slide 29 |
| L02 | **First Sylow Theorem** (existence of p^i subgroups) | §36.8 | 03 slide 29-40 |
| L03 | **Second Sylow Theorem** (all Sylow p-subgroups are conjugate) | §36.10 | |
| L04 | **Third Sylow Theorem** (n_p ≡ 1 mod p, n_p \| \|G\|) | §36.11 | |
| L05 | Class equation | §37.2 | 03 slide 41-45 |
| L06 | Center of p-group is nontrivial | §37.4 | |
| L07 | Groups of order p² are abelian | §37.6 | 04 |
| L08 | Application: classifying groups of small order | §37 | 04 |

---

## World Dependency Graph

```
BasicLean (10)
  ├→ BasicFunctions (6)
  │     └→ EquivalenceRelation (~12)
  │
  └→ Magma (9)
        └→ GroupBasics (~10)
              └→ CosetsAndLagrange (~8)
                    └→ GroupHomo (6)
                          └→ GroupAction (~10)  ← central world
                                └→ Sylow (~8)
```

Total: ~79 levels across 9 worlds.

---

## Fraleigh's Proof Strategy for Sylow (for reference)

### Key Tool: Fixed Point Counting (Thm 36.1)
If G is a p-group acting on finite set X, then |X| ≡ |X^G| (mod p).
This single theorem drives all three Sylow proofs.

### Cauchy's Theorem (Thm 36.3)
- X = {(g1,...,gp) | g1*...*gp = e}, cyclic ⟨σ⟩ acts by rotation
- |X| = |G|^(p-1), so p | |X|
- Fixed points: (a,a,...,a) where a^p = e
- |X^⟨σ⟩| ≡ |X| ≡ 0 (mod p), and (e,...,e) is a fixed point, so ≥p fixed points
- Some a ≠ e has order p

### Normalizer Lemma (Thm 36.6)
- H is p-subgroup, acts on left cosets G/H by left translation
- Fixed cosets are exactly those in N[H]
- So (G:H) ≡ (N[H]:H) (mod p)

### Sylow I (Thm 36.8): Existence
- Induction on i: given H of order p^i with i < n
- p | (G:H), so by normalizer lemma, p | (N[H]:H)
- Cauchy on N[H]/H gives subgroup of order p
- Pullback gives subgroup of order p^(i+1) containing H

### Sylow II (Thm 36.10): Conjugacy
- P2 acts on left cosets of P1
- |L^P2| ≡ |L| = (G:P1) ≢ 0 (mod p)
- So some coset xP1 is fixed by P2
- This gives x⁻¹P2x ≤ P1, and equal cardinality implies P1 = x⁻¹P2x

### Sylow III (Thm 36.11): Counting
- P acts on S = {all Sylow p-subgroups} by conjugation
- S^P = {T | xTx⁻¹ = T for all x ∈ P} = {P} (by Sylow II in N[T])
- |S| ≡ |S^P| = 1 (mod p)
- G acts on S transitively (by Sylow II), so |S| = (G:N[P]) divides |G|

---

## Design Principles

1. **Every proof ≤ 20 tactic steps** — extract trivial parts as lemmas
2. **Students learn proof strategy**, not tedious calculations
3. **Every level has**: Introduction (2-5 sentences), Hints, Conclusion
4. **Trivial lemmas are given for free** — students focus on the interesting steps
5. **Use BasicLean levels as documentation quality template**

## Implementation Priority

1. Fix existing content (documentation, sorry, long proofs) ← IN PROGRESS
2. Restructure BasicGroupTheory → GroupBasics + CosetsAndLagrange
3. Simplify EquivalenceRelation 22 → ~12 levels
4. Expand GroupAction from 3 → ~10 levels
5. Create Sylow world (~8 levels)
6. Polish all levels end-to-end
