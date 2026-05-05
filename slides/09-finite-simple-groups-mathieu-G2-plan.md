# Lecture 09 Plan: Finite Simple Groups Through Three Examples

## Position in the Course

L09 is the **last group theory lecture** before the course pivots to ring
theory and Galois theory. It synthesizes earlier material around a single
question and uses three concrete case studies to make the answer real.

- Builds on L01 (simple groups, $\mathbb Z_p$), L02 (group actions),
  L03/L05 (Sylow), L04 ($A_n$ simple, normalizer), L08 (composition factors,
  Jordan–Hölder).
- Bridges to ring theory via division algebras (octonions) and to Galois
  theory via finite fields (used to define $G_2(\mathbb F_p)$).

## Main Theme

> **Which finite simple groups are there?**
> The full answer is CFSG. Today is **not** a survey of all four families.
> We meet **three concrete examples**, one from each kind of family CFSG
> describes, and use them to feel the texture of the classification.

## Non-Overlap with Earlier Lectures

- Do **not** re-prove $A_n$ simple (L04) or restate Sylow / class equation.
- Do **not** re-derive $\operatorname{PSL}_n(\mathbb F_q)$ orders or
  coincidences from scratch — these were used as examples earlier; only
  compile a quick reference table.
- Do **not** introduce representation theory or character tables — that
  belongs to a later course / further reading.
- Do **not** introduce Lie groups or Lie algebras formally; $G_2$ is
  approached purely as $\operatorname{Aut}(\mathbb O)$.
- Do **not** require $\mathbb F_q$ for prime-power $q$; restrict to
  $\mathbb F_p$ for $p$ prime so no Galois prerequisites are needed. Mention
  that the definition extends to $\mathbb F_q$ once Galois theory is in hand.
- Do **not** include a Quiz slide. Quiz logistics live outside the deck.

## Lecture Flow (≈ 90 min)

1. **Part I — Landscape.** Recall, CFSG statement (no proof), today's
   three examples. (≈ 8 min)

2. **Part II — Example 1: $\operatorname{PSL}_n(\mathbb F_p)$.** Orders,
   Jordan–Dickson simplicity theorem, beautiful coincidences with $A_n$,
   summary. Includes bio slides for **C. Jordan** and **L. E. Dickson**.
   (≈ 18 min)

3. **Part III — Example 2: $M_{12}$.** Sporadic backstory; bio of **É.
   Mathieu** (no portrait available); Steiner systems and motivation;
   $S(5,6,12)$; **explicit block construction via
   $\operatorname{PSL}_2(\mathbb F_{11})$ orbit of
   $\{\infty,1,3,4,5,9\}$**; the two layers of symmetry; $M_{12} =
   \operatorname{Aut}(S(5,6,12))$; full $k$-transitivity definition + lower
   bound; sharp $5$-transitivity classification (Jordan + later); order
   computation; $M_{11}$ as point-stabilizer; outer aut of $S_6$, Golay code
   bridge to $M_{24}$/Monster. (≈ 30 min)

4. **Part IV — Example 3: $G_2$ via the octonions.** Hurwitz's theorem (with
   bio of **A. Hurwitz**); Cayley–Dickson doubling (with bio of **A.
   Cayley**); octonion presentation and Fano plane; tower of automorphism
   groups; Cartan's classification (with bio of **É. Cartan**);
   $G_2(\mathbb F_p)$ definition, order formula
   $p^6(p^6-1)(p^2-1)$, simplicity for $p\ge 3$, the $p=2$ exception
   $G_2(\mathbb F_2)'\cong\operatorname{PSU}_3(\mathbb F_3)$. (≈ 25 min)

5. **Part V — Looking back.** CFSG tree; what the three examples reveal
   about each branch; **References — CFSG/sporadic** and **References —
   exceptional groups**; bridges to ring theory (octonions) and Galois
   (finite fields); what to remember; homework. (≈ 8 min)

## Mathematician Bio Slides

Every named mathematician gets a bio slide with portrait, lifespan, and a
short pointer to their relevant work.

| Person | Slide title | Where | Portrait source |
|---|---|---|---|
| Camille Jordan | "Camille Jordan (1838–1922)" | Part II, after PSL simplicity | `/camille-jordan.jpg` |
| Leonard Dickson | "Leonard Eugene Dickson (1874–1954)" | Part II, after Jordan | `/leonard-dickson.jpg` (MacTutor) |
| Émile Mathieu | "Émile Léonard Mathieu (1835–1890)" | Part III, after Sporadic Simple Groups | none — styled placeholder card |
| Adolf Hurwitz | "Adolf Hurwitz (1859–1919)" | Part IV, after Hurwitz's theorem | `/hurwitz.jpg` (Wikimedia) |
| Arthur Cayley | "Arthur Cayley (1821–1895)" | Part IV, after Cayley–Dickson Doubling | `/cayley.jpg` |
| Élie Cartan | "Élie Cartan (1869–1951)" | Part IV, after Why $G_2$ Is "Exceptional" | `/elie-cartan.png` (Wikimedia, FR) |

## Minimal Learning Outcomes

By the end of L09, students should be able to:

1. State CFSG (the four families) and place named groups into them.
2. Read off $|\operatorname{GL}_n(\mathbb F_p)|$, $|\operatorname{SL}_n|$,
   $|\operatorname{PSL}_n|$ and recognize the small-$(n,p)$ exceptions.
3. Define a Steiner system $S(t,k,v)$ and explain why
   $\operatorname{Aut}(S(t,k,v))$ tends to be $t$-transitive.
4. Define $k$-transitivity, prove the lower bound
   $|G|\ge n(n-1)\cdots(n-k+1)$, and state the sharp $5$-transitivity
   classification.
5. Compute $|M_{12}|=95\,040$ from sharp $5$-transitivity, and explain how
   the $132$ blocks of $S(5,6,12)$ arise as one
   $\operatorname{PSL}_2(\mathbb F_{11})$-orbit.
6. List the $4$ normed division algebras over $\mathbb R$ and their
   automorphism groups, ending at $\operatorname{Aut}(\mathbb O)=G_2$.
7. Write the order formula $|G_2(\mathbb F_p)|=p^6(p^6-1)(p^2-1)$ and explain
   why $p=2$ is the small-characteristic exception.

## Homework

- **HW 1 ($M_{12}$).** Show that the stabilizer of one point in a
  $k$-transitive group on $n$ points is $(k-1)$-transitive on the remaining
  $n-1$ points; deduce $|M_{11}|=7920$.
- **HW 2 (octonions).** Verify that an automorphism of $\mathbb O$ fixes
  $1$, commutes with conjugation, preserves the norm; conclude
  $G_2\subseteq\operatorname{O}(7)$.
- **HW 3 ($G_2$ orders).** Compute $|G_2(\mathbb F_3)|$ and
  $|G_2(\mathbb F_5)|$; verify $|G_2(\mathbb F_2)|=12\,096=2\cdot 6048$ and
  identify $6048=|\operatorname{PSU}_3(\mathbb F_3)|$.
