---
title: "MAT205: Abstract Algebra II — Lecture 1"
math: katex
---

# MAT205: Abstract Algebra II

<br/>

**Ma, Jia-Jun** — Xiamen University Malaysia

*Textbook*: Fraleigh, *A First Course in Abstract Algebra*

*Prerequisites*: MAT211 (Abstract Algebra I)

---

# Assessment

| Component | Weight | Details |
|-----------|--------|---------|
| Assignments | 30% | 2 assignments, 15% each |
| Quizzes | 10% | 2 quizzes, 5% each |
| Midterm Exam | 20% | Covers Part I (Group Theory) |
| Final Exam | 40% | Cumulative |

---

# Course Outline

<div style="display: flex; gap: 3rem;">
<div style="flex: 1;">

**Part I: Advanced Group Theory**

1. Review of basics
2. Subnormal series & solvable groups
3. Sylow theorems
4. Applications of Sylow theorems
5. Free groups & free abelian groups

</div>
<div style="flex: 1;">

**Part II: Galois Theory**

6. Field extensions
7. Algebraic extensions
8. Finite fields
9. Field automorphisms
10. Separable extensions
11. Galois theory I & II
12. Factorization in integral domains

</div>
</div>

<br/>

**Midterm**: after Part I &nbsp;&nbsp;|&nbsp;&nbsp; **Final**: cumulative (Part I + II)

---

# Recall: What is a Group?

<div style="display: flex; gap: 2rem;">
<div style="flex: 1;">

A **binary operation** on $S$ is a map $\cdot : S \times S \to S$.

<v-click>

A **group** $(G, \cdot)$ satisfies:

1. **Associativity**: $(ab)c = a(bc)$
2. **Identity**: $\exists\, e$ s.t. $ea = ae = a$
3. **Inverse**: $\forall\, a,\, \exists\, a^{-1}$ s.t. $aa^{-1} = a^{-1}a = e$

</v-click>

<v-click>

**Convention**: Write $ab$ for $a \cdot b$.

</v-click>

</div>
<div style="flex: 0 0 auto;">

| Structure | Axioms |
|-----------|--------|
| **Magma** | closure |
| **Semigroup** | + associativity |
| **Monoid** | + identity |
| **Group** | + inverses |

</div>
</div>

---

# Examples of Groups

| Group | Operation | Identity | Abelian? |
|-------|-----------|----------|----------|
| $(\mathbb{Z}, +)$ | addition | $0$ | Yes |
| $(\mathbb{Q}^*, \times)$ | multiplication | $1$ | Yes |
| $(S_n, \circ)$ | permutation composition | $\text{id}$ | No ($n \geq 3$) |
| $(\mathbb{Z}/n\mathbb{Z}, +)$ | addition mod $n$ | $\bar{0}$ | Yes |
| $(GL_n(\mathbb{R}), \times)$ | matrix multiplication | $I_n$ | No ($n \geq 2$) |
| $SL_n(\mathbb{Z})$ | matrix multiplication | $I_n$ | No ($n \geq 2$) |

<v-click>

**Abelian group**: $G$ is **abelian** if $ab = ba$ for all $a, b \in G$.

</v-click>

<v-click>

$SL_n(\mathbb{Z}) = \{ A \in M_n(\mathbb{Z}) \mid \det(A) = 1 \}$ — the **special linear group** over $\mathbb{Z}$.

</v-click>

---

# $SL_n(\mathbb{Z})$ is a Group

**Why is $SL_n(\mathbb{Z})$ a group?** Under matrix multiplication:

<v-click>

- **Closure**: $\det(AB) = \det(A)\det(B) = 1 \cdot 1 = 1$ $\checkmark$

</v-click>

<v-click>

- **Associativity**: matrix multiplication is associative $\checkmark$
- **Identity**: $\det(I_n) = 1$ $\checkmark$

</v-click>

<v-click>

- **Inverse**: $\det(A) = 1 \implies A^{-1}$ has integer entries (Cramer's rule: $A^{-1} = \text{adj}(A)/\det(A)$) $\checkmark$

</v-click>

<v-click>

In fact, $SL_n(\mathbb{Z})$ is the **kernel** of $\det : GL_n(\mathbb{R}) \to \mathbb{R}^*$.

**Exercise.** Use the one-step subgroup criterion to prove $SL_n(\mathbb{Z}) \leq GL_n(\mathbb{R})$.

</v-click>

---

# $SL_2(\mathbb{Z})$ and Modular Forms

$SL_2(\mathbb{Z})$ acts on the **upper half-plane** $\mathbb{H}$ by Mobius transformations:

$$\mathbb{H} = \{z \in \mathbb{C} \mid \operatorname{Im}(z) > 0\}, \qquad \begin{pmatrix} a & b \\ c & d \end{pmatrix} \cdot z = \frac{az + b}{cz + d}$$

<div style="display: flex; gap: 1rem; align-items: center; margin-top: 0.5rem;">
<div style="flex: 0 0 auto;">

<img src="/fundamental-domain.svg" style="height: 200px; background: white;" />

</div>
<div style="flex: 1; font-size: 0.95rem;">

<v-click>

A **modular form** of weight $k$: holomorphic $f: \mathbb{H} \to \mathbb{C}$ with
$$f\!\left(\frac{az+b}{cz+d}\right) = (cz+d)^k f(z)$$

</v-click>

<v-click>

Connects to: **number theory** (counting arithmetic objects), **Fermat's Last Theorem** (Wiles 1995), **string theory** (partition functions).

</v-click>

</div>
</div>

---

# Non-Examples: Which axiom fails?

Which of the following are groups? **Which axiom fails?**

| Structure | Operation |
|-----------|-----------|
| $(\mathbb{Z}, \times)$ | multiplication |
| $(\mathbb{N}, +)$ | addition |
| $(M_n(\mathbb{R}), \times)$ | matrix multiplication |
| $(\mathbb{Z}, -)$ | subtraction |

---

# Non-Examples: Answers

<div style="font-size: 0.95rem;">

| Structure | Fails | Type |
|-----------|-------|------|
| $(\mathbb{Z}, \times)$ | **no inverses** — $2^{-1} \notin \mathbb{Z}$ | monoid |
| $(\mathbb{N}, +)$ | **no inverses** — $-3 \notin \mathbb{N}$ | monoid |
| $(M_n(\mathbb{R}), \times)$ | **no inverses** — singular matrices | monoid |
| $(\mathbb{Z}, -)$ | **not associative** — $(1\!-\!1)\!-\!1 \neq 1\!-\!(1\!-\!1)$ | magma |

</div>

**Monoid** = associative + identity, but no inverses. **Magma** = just closure.

---

# Subgroups

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1;">

**Definition.** A nonempty subset $H \subseteq G$ is a **subgroup** of $G$ (written $H \leq G$) if $H$ is itself a group under the same operation.

<v-click>

**One-step subgroup criterion.** $H \leq G$ if and only if $H \neq \emptyset$ and
$$a, b \in H \implies ab^{-1} \in H$$

</v-click>

<v-click>

**Two-step criterion.** $H \leq G$ if and only if:
1. $a, b \in H \implies ab \in H$ (closed under multiplication)
2. $a \in H \implies a^{-1} \in H$ (closed under inverse)

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/lagrange.jpg" style="height: 160px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">Lagrange (1736–1813)</div>

</div>
</div>

<div style="font-size: 0.85rem; opacity: 0.7; margin-top: 0.5rem;">

Lagrange's 1770 work on permutations of polynomial roots laid the groundwork for subgroup theory.

</div>

---

# Subgroup Examples

**Example 1.** $k\mathbb{Z} = \{kn \mid n \in \mathbb{Z}\} \leq (\mathbb{Z}, +)$ for any $k \in \mathbb{Z}$.

*Proof.* If $a = km$ and $b = kn$, then $a - b = k(m-n) \in k\mathbb{Z}$. $\square$

<v-click>

**Subgroup inclusion $\leftrightarrow$ divisibility:** $m\mathbb{Z} \subseteq k\mathbb{Z} \iff k \mid m$.

$$6\mathbb{Z} \subset 3\mathbb{Z} \subset \mathbb{Z}, \qquad 6\mathbb{Z} \subset 2\mathbb{Z} \subset \mathbb{Z}$$

</v-click>

<v-click>

The **lattice of subgroups** of $(\mathbb{Z}, +)$ is exactly the **divisibility lattice** of $\mathbb{N}$.

A **lattice** is a partially ordered set where every pair has a **join** (least upper bound) and **meet** (greatest lower bound). For subgroups of $G$: meet = $H \cap K$, join = $\langle H, K \rangle$.

</v-click>

<v-click>

**More examples:** $A_n \leq S_n$ (alternating group), $SL_n(\mathbb{Z}) \leq GL_n(\mathbb{R})$.

**Definition.** The **center** of $G$ is $Z(G) = \{g \in G \mid gx = xg \text{ for all } x \in G\} \leq G$.

**Exercise.** Verify that $Z(G)$ is a subgroup using the two-step criterion.

</v-click>

---

# The Center of a Group

**Recall.** $Z(G) = \{g \in G \mid gx = xg \text{ for all } x \in G\}$.

<v-click>

**Example 1.** $Z(GL_n(\mathbb{R})) = \{\lambda I_n \mid \lambda \in \mathbb{R}^*\} \cong \mathbb{R}^*$ (scalar matrices).

*Proof sketch.* If $A$ commutes with every invertible matrix, take $A E_{ij} = E_{ij} A$ for elementary matrices $\implies$ $A$ is diagonal $\implies$ all diagonal entries equal. $\square$

</v-click>

<v-click>

**Example 2.** $Z(S_n) = \{e\}$ for $n \geq 3$ (the symmetric group has trivial center).

</v-click>

<v-click>

**Example 3.** $Z(D_n) = \{e, r^{n/2}\}$ if $n$ even; $Z(D_n) = \{e\}$ if $n$ odd.

</v-click>

<v-click>

**Remark.** The quotient $G/Z(G)$ is called the **inner automorphism group** $\operatorname{Inn}(G)$. Note $PGL_n(\mathbb{R}) = GL_n(\mathbb{R})/Z(GL_n(\mathbb{R}))$ — the **projective linear group**.

</v-click>

---

# Classification of Subgroups of $\mathbb{Z}$

**Theorem.** Every subgroup of $(\mathbb{Z}, +)$ is of the form $k\mathbb{Z}$ for some $k \in \mathbb{N}$.

<v-click>

*Proof sketch.* Let $H \leq \mathbb{Z}$. If $H = \{0\}$, then $H = 0\mathbb{Z}$. Otherwise, $H$ contains a smallest positive element $k$ (well-ordering). Then $H = k\mathbb{Z}$.

</v-click>

<v-click>

This gives a **bijection**:
$$\left\{\text{subgroups of } \mathbb{Z}\right\} \xleftrightarrow{1:1} \mathbb{N}, \qquad k\mathbb{Z} \longleftrightarrow k$$

</v-click>

<v-click>

Under this correspondence:
- $k\mathbb{Z} \subseteq m\mathbb{Z} \iff m \mid k$ (inclusion $\leftrightarrow$ divisibility)
- $k\mathbb{Z} \cap m\mathbb{Z} = \operatorname{lcm}(k,m)\mathbb{Z}$
- $k\mathbb{Z} + m\mathbb{Z} = \gcd(k,m)\mathbb{Z}$
- $\mathbb{Z}/k\mathbb{Z} \cong \mathbb{Z}_k$ (quotient $\leftrightarrow$ modular arithmetic)

</v-click>

<v-click>

**Remark.** $\mathbb{Z}$ is a **principal ideal domain** (PID) — every subgroup (= ideal) is generated by a single element. We will return to PIDs in Lecture 25 (Ring Theory).

</v-click>

---

# Cosets

**Definition.** Let $H \leq G$ and $g \in G$. The **left coset** of $H$ by $g$ is:
$$gH = \{gh \mid h \in H\}$$

<v-click>

**Key properties:**
1. $g \in gH$ (since $e \in H$)
2. $gH = kH \iff k^{-1}g \in H$

</v-click>

<v-click>

3. Two cosets are either **equal** or **disjoint**
4. $|gH| = |H|$ for any $g \in G$

</v-click>

<v-click>

The coset relation $a \sim b \iff a^{-1}b \in H$ is an **equivalence relation** on $G$.
Cosets are the equivalence classes of this relation.

</v-click>

---

# The Coset Space and Lagrange's Theorem

**Definition.** The set of all left cosets is the **coset space**:
$$G/H = \{gH \mid g \in G\}$$

<v-click>

The number of cosets is the **index**: $[G:H] = |G/H|$.

</v-click>

<div style="display: flex; gap: 1.5rem; margin-top: 0.5rem;">
<div style="flex: 1;">

<v-click>

**Lagrange's Theorem.** If $G$ is a finite group and $H \leq G$, then
$$|G| = [G:H] \cdot |H|$$

In particular, $|H|$ divides $|G|$.

</v-click>

<v-click>

**Corollary.** The order of any element divides $|G|$. Hence $g^{|G|} = e$ for all $g \in G$.

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/lagrange.jpg" style="height: 140px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">Lagrange (1736–1813)</div>

</div>
</div>

---

# Example: Cosets in $\mathbb{Z}/6\mathbb{Z}$

Let $G = \mathbb{Z}/6\mathbb{Z} = \{\bar{0}, \bar{1}, \bar{2}, \bar{3}, \bar{4}, \bar{5}\}$ and $H = \{\bar{0}, \bar{3}\}$.

<v-click>

The left cosets of $H$:

| Coset | Elements |
|-------|----------|
| $\bar{0} + H$ | $\{\bar{0}, \bar{3}\}$ |
| $\bar{1} + H$ | $\{\bar{1}, \bar{4}\}$ |
| $\bar{2} + H$ | $\{\bar{2}, \bar{5}\}$ |

</v-click>

<v-click>

So $[G:H] = 3$, and indeed $|G| = 6 = 3 \times 2 = [G:H] \cdot |H|$. $\checkmark$

</v-click>

---

# Consequences of Lagrange's Theorem

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 1.1rem;">

**Corollary 1.** If $|G| = p$ (prime), then $G \cong \mathbb{Z}/p\mathbb{Z}$.

*Proof.* Take any $g \neq e$. Then $|\langle g \rangle|$ divides $p$, so $|\langle g \rangle| = p$, hence $\langle g \rangle = G$. $\square$

<v-click>

**Corollary 2.** (Fermat) If $p$ prime, $\gcd(a, p) = 1$, then $a^{p-1} \equiv 1 \pmod{p}$.

*Proof.* Apply Lagrange to $(\mathbb{Z}/p\mathbb{Z})^*$, order $p-1$. $\square$

</v-click>

<v-click>

**Corollary 3.** (Euler) If $\gcd(a, n) = 1$, then $a^{\varphi(n)} \equiv 1 \pmod{n}$.

*Proof.* Apply Lagrange to $(\mathbb{Z}/n\mathbb{Z})^*$, order $\varphi(n)$. $\square$

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center; gap: 0.5rem;">

<img src="/fermat.jpg" style="height: 150px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">Fermat (1607–1665)</div>

<img src="/euler.jpg" style="height: 150px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">Euler (1707–1783)</div>

</div>
</div>

---

# Group Homomorphisms

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1;">

> *"Rather than analyzing objects, we should concentrate on **morphisms** between them."* — Grothendieck

<v-click>

**Definition.** A map $f: G \to H$ is a **group homomorphism** if
$$f(ab) = f(a)f(b) \quad \text{for all } a, b \in G$$

</v-click>

<v-click>

**Automatic consequences:**
- $f(e_G) = e_H$
- $f(a^{-1}) = f(a)^{-1}$

</v-click>

<v-click>

**Exercise.** Prove these two consequences from the definition.

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/grothendieck.jpg" style="height: 240px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">A. Grothendieck (1928–2014)</div>

</div>
</div>

---

# Kernel and Image

**Definition.** For a homomorphism $f: G \to H$:
- **Kernel**: $\ker(f) = \{g \in G \mid f(g) = e_H\}$
- **Image**: $\operatorname{im}(f) = \{f(g) \mid g \in G\}$

<v-click>

**Key facts:**
1. $\ker(f) \leq G$ and $\operatorname{im}(f) \leq H$

</v-click>

<v-click>

2. $f$ is injective $\iff$ $\ker(f) = \{e\}$

</v-click>

<v-click>

3. $\ker(f)$ is a **normal** subgroup of $G$

**Exercise.** Prove fact 3: if $g \in G$ and $n \in \ker(f)$, show $gng^{-1} \in \ker(f)$.

</v-click>

---

# Normal Subgroups

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 0.95rem;">

**Definition.** $N \leq G$ is **normal** ($N \trianglelefteq G$) if $gNg^{-1} = N$ for all $g \in G$.

<v-click>

**Equivalent conditions:**
1. $gNg^{-1} \subseteq N$ for all $g \in G$
2. $gN = Ng$ for all $g \in G$ (left cosets = right cosets)
3. $N = \ker(f)$ for some homomorphism $f$

</v-click>

<v-click>

**Why normal?** Coset multiplication becomes well-defined: $(gN)(hN) = (gh)N$.
This makes $G/N$ a group — the **quotient group**.

</v-click>

<v-click>

<div style="font-size: 0.85rem; opacity: 0.7; margin-top: 0.3rem;">Galois introduced normal subgroups in 1832, connecting them to solvability of polynomials.</div>

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/galois.jpg" style="height: 160px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">Galois (1811–1832)</div>

</div>
</div>

---

# The Isomorphism Theorems

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 0.95rem;">

**First Isomorphism Theorem.** If $f: G \to H$ is a homomorphism, then
$$G / \ker(f) \cong \operatorname{im}(f)$$

<v-click>

$$\begin{CD} G @>{f}>> H \\ @V{\pi}VV @AA{\bar{f}}A \\ G/\ker(f) @= \operatorname{im}(f) \end{CD}$$

</v-click>

<v-click>

**Second Isomorphism Theorem.** If $A \leq G$ and $B \trianglelefteq G$, then
$$A / (A \cap B) \cong AB / B$$

</v-click>

<v-click>

**Third Isomorphism Theorem.** If $N \subseteq M$ are both normal in $G$, then
$$(G/N) / (M/N) \cong G/M$$

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/noether.jpg" style="height: 180px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">Emmy Noether (1882–1935)</div>

</div>
</div>

<div style="font-size: 0.85rem; opacity: 0.7;">

Noether formalized the isomorphism theorems in abstract form, establishing modern algebra as a discipline.

</div>

---

# Simple Groups

**Definition.** A group $G$ is **simple** if its only normal subgroups are $\{e\}$ and $G$.

<v-click>

**Examples:**
- $\mathbb{Z}/p\mathbb{Z}$ for $p$ prime (abelian simple groups)
- $A_n$ for $n \geq 5$ (non-abelian simple groups)

</v-click>

<v-click>

**Theorem.** The only finite abelian simple groups are $\mathbb{Z}/p\mathbb{Z}$ for $p$ prime.

</v-click>

<v-click>

*Proof.* If $G$ is abelian, every subgroup is normal. If $G$ is simple, it has no proper nontrivial subgroups. Take $g \neq e$; then $\langle g \rangle = G$. If $|G| = mn$ with $1 < m, n$, then $\langle g^m \rangle$ is a proper subgroup — contradiction. So $|G|$ is prime. $\square$

</v-click>

---

# Classification of Finite Simple Groups

The **CFSG** (completed ~2004, tens of thousands of pages) states:

<v-click>

Every finite simple group is one of:
1. $\mathbb{Z}/p\mathbb{Z}$ (cyclic of prime order)
2. $A_n$ for $n \geq 5$ (alternating groups)
3. A group of **Lie type** (e.g., $PSL_n(\mathbb{F}_q)$)
4. One of **26 sporadic groups** (e.g., the Monster group, $|M| \approx 8 \times 10^{53}$)

</v-click>

<v-click>

The Monster group has dimension 196,883 in its smallest faithful representation — its connections to modular functions are known as **"monstrous moonshine"** (proved by Borcherds, 1992).

</v-click>

<v-click>

**This course**: We will use simple groups as building blocks via **composition series** (next lecture).

</v-click>

---

# Exercises

**Exercise 1.** Let $G$ be a group of order $2p$ where $p$ is an odd prime. Show that $G$ has a normal subgroup of order $p$.

**Exercise 2.** Prove that if $f: G \to H$ is a surjective homomorphism and $G$ is abelian, then $H$ is abelian.

**Exercise 3.** Show that $A_4$ has no subgroup of order 6. (The converse of Lagrange's theorem is false!)

**Exercise 4.** Let $H \leq G$ with $[G:H] = 2$. Prove that $H \trianglelefteq G$.

**Exercise 5.** If $|G| = p^2$ for a prime $p$, show that $G$ is abelian. *(Hint: Consider $Z(G)$.)*

**Exercise 6.** Prove that $SL_n(\mathbb{Z})$ is a group under matrix multiplication. *(Hint: Use $\det(AB) = \det(A)\det(B)$ and Cramer's rule for integer invertibility.)*

---

# Looking Ahead

In this course, we will study:

1. **Subnormal series** — decomposing groups into simple factors
2. **Sylow theorems** — existence and structure of $p$-subgroups
3. **Free groups** — universal constructions
4. **Field extensions** — moving from groups to fields
5. **Galois theory** — connecting field extensions to group theory

**Next lecture**: Subnormal series and solvable groups.

---
layout: center
---

# Questions?
