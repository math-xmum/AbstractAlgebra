# Lecture 08 Plan: Subnormal Series, Solvable and Nilpotent Groups

## Main Narrative

Use chains of normal inclusions to study successive quotient groups.

The lecture contains three definitions and their standard criteria:

1. Subnormal and composition series.
2. Solvable groups: existence of a subnormal series with abelian factors; equivalently the derived series terminates.
3. Nilpotent groups: existence of a central series; equivalently the lower central series terminates.

## Pedagogical Choices

- Use definitions, theorem statements, and explicit examples.
- State Jordan-Holder and its consequence for composition factors.
- Use a small set of examples: `S_3`, `D_4`, `A_5`, and the abelian baseline `Z_n`.
- Mention unitriangular groups only as a structural family, not as another repeated running example.
- Link to previous lectures:
  - Sylow: finite nilpotent groups are direct products of Sylow subgroups.
  - Free groups: quotient maps can detect non-solvability, but this is not a main example here.
  - Abelianization: already covered in Lecture 07, so do not review it as a separate topic.

## Lecture Flow

1. Extensions and series
   - Short exact sequence viewpoint.
   - Normal vs subnormal series.
   - Successive factor groups.

2. Composition series
   - Simple groups.
   - Composition series and composition length.
   - Explicit calculations for `S_3`, `Z_12`, and direct products.
   - Jordan-Holder theorem.
   - Composition factors are not enough to reconstruct the group.

3. Solvable groups
   - Main definition via a subnormal series with abelian quotients.
   - Commutator condition for abelian factors.
   - Derived series, defined inductively, as the computational criterion.
   - Examples: `S_3` and `A_5`.
   - Composition-factor test for finite groups.
   - Galois theorem on solvability by radicals over `Q`.
   - Radical extensions, generic polynomial application, and Burnside's `p^a q^b` theorem.

4. Nilpotent groups
   - Center first, then upper and lower central series, both defined inductively.
   - Central series, then nilpotent groups.
   - Nilpotency class.
   - Examples: abelian groups, `D_4`, and `UT_n`.
   - Finite `p`-groups and Sylow product criterion.
   - Nilpotent implies solvable.

5. Summary
   - Implication chain: abelian -> nilpotent -> solvable -> all groups.
   - Finite-group criteria.

## Assets

- TikZ-generated SVGs:
  - `series-ladder.svg`
  - `jordan-holder-two-series.svg`
  - `central-derived-series.svg`
  - `group-hierarchy.svg`
- Photos:
  - `camille-jordan.jpg`
  - `otto-holder.jpg`
  - `galois.jpg`
  - `william-burnside.jpeg`
