---
title: "MAT205: Abstract Algebra II — Lecture 1"
math: katex
---

# MAT205: Abstract Algebra II

## 1. Review of Basics

<div style="margin-top: 3rem; font-size: 1.3rem; opacity: 0.6;">

**Ma, Jia-Jun**

Xiamen University Malaysia

</div>

---

# Recall: What is a Group?

<div style="display: flex; gap: 2rem;">
<div style="flex: 1;">

A **group** $(G, \cdot)$ is a set with a binary operation satisfying:

1. **Associativity**: $(a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. **Identity**: $\exists\, e \in G$ s.t. $ea = ae = a$
3. **Inverse**: $\forall\, a,\, \exists\, a^{-1}$ s.t. $aa^{-1} = a^{-1}a = e$

<v-click>

**Convention**: Write $ab$ instead of $a \cdot b$.

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

| Group | Operation | Identity |
|-------|-----------|----------|
| $(\mathbb{Z}, +)$ | addition | $0$ |
| $(\mathbb{Q}^*, \times)$ | multiplication | $1$ |
| $(S_n, \circ)$ | composition of permutations | $\text{id}$ |
| $(\mathbb{Z}/n\mathbb{Z}, +)$ | addition mod $n$ | $\bar{0}$ |
| $(GL_n(\mathbb{R}), \times)$ | matrix multiplication | $I_n$ |

<v-click>

**Abelian group**: $G$ is **abelian** if $ab = ba$ for all $a, b \in G$.

Among the examples above, $S_n$ for $n \geq 3$ and $GL_n(\mathbb{R})$ for $n \geq 2$ are **not** abelian.

</v-click>

---

# Example: $SL_n(\mathbb{Z})$

**Definition.** The **special linear group** over $\mathbb{Z}$:
$$SL_n(\mathbb{Z}) = \left\{ A \in M_n(\mathbb{Z}) \mid \det(A) = 1 \right\}$$

<v-click>

**Why is this a group?** Under matrix multiplication:
- **Closure**: $\det(AB) = \det(A)\det(B) = 1 \cdot 1 = 1$ $\checkmark$
- **Associativity**: matrix multiplication is associative $\checkmark$
- **Identity**: $I_n$ has $\det(I_n) = 1$ $\checkmark$
- **Inverse**: $\det(A) = 1 \implies A^{-1}$ has integer entries (by Cramer's rule) $\checkmark$

</v-click>

<v-click>

**Exercise.** Prove that $SL_n(\mathbb{Z}) \leq GL_n(\mathbb{R})$ is a subgroup. In fact, it is the kernel of
$$\det : GL_n(\mathbb{R}) \to \mathbb{R}^*$$

</v-click>

---

# $SL_2(\mathbb{Z})$ and Modular Forms

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1;">

$SL_2(\mathbb{Z})$ acts on the **upper half-plane** $\mathbb{H} = \{z \in \mathbb{C} \mid \operatorname{Im}(z) > 0\}$:

$$\begin{pmatrix} a & b \\ c & d \end{pmatrix} \cdot z = \frac{az + b}{cz + d}$$

<v-click>

A **modular form** of weight $k$ is a holomorphic $f: \mathbb{H} \to \mathbb{C}$ with:
$$f\!\left(\frac{az+b}{cz+d}\right) = (cz+d)^k f(z)$$

</v-click>

<v-click>

Modular forms connect to:
- **Number theory** — Fourier coefficients count arithmetic objects
- **Fermat's Last Theorem** — Wiles' modularity theorem (1995)
- **String theory** — partition functions

</v-click>

</div>
<div style="flex: 0 0 420px; display: flex; flex-direction: column; align-items: center; gap: 0.5rem;">

<img src="/fundamental-domain.svg" style="width: 180px; background: white; border-radius: 4px;" />

<img src="/tessellation.svg" style="width: 420px; background: white; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.5;">Fundamental domain and tessellation of $\mathbb{H}$ by $SL_2(\mathbb{Z})$</div>

</div>
</div>

---

# Non-Examples

Not every algebraic structure is a group:

- $(\mathbb{Z}, \times)$: No inverses — $2$ has no multiplicative inverse in $\mathbb{Z}$
- $(\mathbb{N}, +)$: No inverses — no negative numbers
- $(M_n(\mathbb{R}), \times)$: Singular matrices have no inverse

<v-click>

**Key question**: Given a set with a binary operation, which axioms fail?

</v-click>

---

# Subgroups

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

---

# Subgroup Examples

**Example 1.** $k\mathbb{Z} = \{kn \mid n \in \mathbb{Z}\} \leq (\mathbb{Z}, +)$ for any $k \in \mathbb{Z}$.

*Proof.* If $a = km$ and $b = kn$, then $a - b = k(m-n) \in k\mathbb{Z}$. $\square$

<v-click>

**Example 2.** The alternating group $A_n = \{\sigma \in S_n \mid \sigma \text{ is even}\} \leq S_n$.

</v-click>

<v-click>

**Example 3.** The center $Z(G) = \{g \in G \mid gx = xg \text{ for all } x \in G\} \leq G$.

</v-click>

<v-click>

**Exercise.** Verify that $Z(G)$ is indeed a subgroup using the two-step criterion.

</v-click>

---

# Cosets

**Definition.** Let $H \leq G$ and $g \in G$. The **left coset** of $H$ by $g$ is:
$$gH = \{gh \mid h \in H\}$$

<v-click>

**Key properties:**
1. $g \in gH$ (since $e \in H$)
2. $gH = kH \iff k^{-1}g \in H$
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

The number of cosets is the **index**: $[G:H] = |G/H|$.

<v-click>

**Lagrange's Theorem.** If $G$ is a finite group and $H \leq G$, then
$$|G| = [G:H] \cdot |H|$$

In particular, $|H|$ divides $|G|$.

</v-click>

<v-click>

**Corollary.** The order of any element divides $|G|$. Hence $g^{|G|} = e$ for all $g \in G$.

</v-click>

---

# Example: Cosets in $\mathbb{Z}/6\mathbb{Z}$

Let $G = \mathbb{Z}/6\mathbb{Z} = \{\bar{0}, \bar{1}, \bar{2}, \bar{3}, \bar{4}, \bar{5}\}$ and $H = \{\bar{0}, \bar{3}\}$.

The left cosets of $H$:

| Coset | Elements |
|-------|----------|
| $\bar{0} + H$ | $\{\bar{0}, \bar{3}\}$ |
| $\bar{1} + H$ | $\{\bar{1}, \bar{4}\}$ |
| $\bar{2} + H$ | $\{\bar{2}, \bar{5}\}$ |

<v-click>

So $[G:H] = 3$, and indeed $|G| = 6 = 3 \times 2 = [G:H] \cdot |H|$. $\checkmark$

</v-click>

---

# Consequences of Lagrange's Theorem

**Corollary 1.** If $|G| = p$ (prime), then $G \cong \mathbb{Z}/p\mathbb{Z}$.

*Proof.* Take any $g \neq e$. Then $|\langle g \rangle|$ divides $p$, so $|\langle g \rangle| = p$, hence $\langle g \rangle = G$. $\square$

<v-click>

**Corollary 2.** (Fermat's little theorem) If $p$ is prime and $\gcd(a, p) = 1$, then $a^{p-1} \equiv 1 \pmod{p}$.

*Proof.* Apply Lagrange to $(\mathbb{Z}/p\mathbb{Z})^*$, which has order $p-1$. $\square$

</v-click>

<v-click>

**Corollary 3.** (Euler's theorem) If $\gcd(a, n) = 1$, then $a^{\varphi(n)} \equiv 1 \pmod{n}$.

</v-click>

---

# Group Homomorphisms

> *"Rather than analyzing objects, we should concentrate on **morphisms** between them."* — Grothendieck

**Definition.** A map $f: G \to H$ is a **group homomorphism** if
$$f(ab) = f(a)f(b) \quad \text{for all } a, b \in G$$

<v-click>

**Automatic consequences:**
- $f(e_G) = e_H$
- $f(a^{-1}) = f(a)^{-1}$

</v-click>

<v-click>

**Exercise.** Prove these two consequences from the definition.

</v-click>

---

# Kernel and Image

**Definition.** For a homomorphism $f: G \to H$:
- **Kernel**: $\ker(f) = \{g \in G \mid f(g) = e_H\}$
- **Image**: $\operatorname{im}(f) = \{f(g) \mid g \in G\}$

<v-click>

**Key facts:**
1. $\ker(f) \leq G$ and $\operatorname{im}(f) \leq H$
2. $f$ is injective $\iff$ $\ker(f) = \{e\}$
3. $\ker(f)$ is a **normal** subgroup of $G$

</v-click>

<v-click>

**Exercise.** Prove fact 3: if $g \in G$ and $n \in \ker(f)$, show $gng^{-1} \in \ker(f)$.

</v-click>

---

# Normal Subgroups

**Definition.** A subgroup $N \leq G$ is **normal** (written $N \trianglelefteq G$) if
$$gNg^{-1} = N \quad \text{for all } g \in G$$

<v-click>

**Equivalent conditions:**
1. $gNg^{-1} \subseteq N$ for all $g \in G$
2. $gN = Ng$ for all $g \in G$ (left cosets = right cosets)
3. $N = \ker(f)$ for some homomorphism $f$

</v-click>

<v-click>

**Why normal?** If $N \trianglelefteq G$, then coset multiplication is well-defined:
$$(gN)(hN) = (gh)N$$
This makes $G/N$ into a group — the **quotient group**.

</v-click>

---

# The Isomorphism Theorems

**First Isomorphism Theorem.** If $f: G \to H$ is a homomorphism, then
$$G / \ker(f) \cong \operatorname{im}(f)$$

<v-click>

$$G \xrightarrow{\quad f \quad} H$$
$$\downarrow \pi \qquad \nearrow \bar{f}$$
$$G/\ker(f)$$

</v-click>

<v-click>

**Second Isomorphism Theorem.** If $A \leq G$ and $B \trianglelefteq G$, then
$$A / (A \cap B) \cong AB / B$$

</v-click>

<v-click>

**Third Isomorphism Theorem.** If $N \subseteq M$ are both normal in $G$, then
$$(G/N) / (M/N) \cong G/M$$

</v-click>

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

*Proof.* If $G$ is abelian, every subgroup is normal. If $G$ is simple, it has no proper nontrivial subgroups. Take $g \neq e$; then $\langle g \rangle = G$. If $|G| = mn$ with $1 < m, n$, then $\langle g^m \rangle$ is a proper subgroup — contradiction. So $|G|$ is prime. $\square$

</v-click>

---

# Classification of Finite Simple Groups

The **CFSG** (completed ~2004, tens of thousands of pages) states:

Every finite simple group is one of:
1. $\mathbb{Z}/p\mathbb{Z}$ (cyclic of prime order)
2. $A_n$ for $n \geq 5$ (alternating groups)
3. A group of **Lie type** (e.g., $PSL_n(\mathbb{F}_q)$)
4. One of **26 sporadic groups** (e.g., the Monster group, $|M| \approx 8 \times 10^{53}$)

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

<v-click>

**Next lecture**: Subnormal series and solvable groups.

</v-click>

---
layout: center
---

# Questions?
