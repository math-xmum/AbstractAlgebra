---
title: "MAT205: Abstract Algebra II — Lecture 2"
math: katex
---

# MAT205: Abstract Algebra II

## 2. Group Actions

<br/>

**Ma, Jia-Jun** — Xiamen University Malaysia

---

# What is a Group Action?

**Definition.** A (left) **group action** of $G$ on a set $X$ is a map $G \times X \to X$, written $(g, x) \mapsto g \cdot x$, satisfying:

<v-click>

1. **Identity**: $e \cdot x = x$ for all $x \in X$

</v-click>

<v-click>

2. **Compatibility**: $(gh) \cdot x = g \cdot (h \cdot x)$ for all $g, h \in G$, $x \in X$

</v-click>

<v-click>

Equivalently, a group action is a homomorphism $\varphi: G \to \operatorname{Sym}(X)$.

Each $g \in G$ defines a **bijection** $x \mapsto g \cdot x$ on $X$.

</v-click>

---

# Group Actions $\leftrightarrow$ Homomorphisms

A group action $G \curvearrowright X$ is **the same thing** as a homomorphism $\varphi: G \to \operatorname{Sym}(X)$.

<v-click>

**Action $\to$ homomorphism:** Given $G \curvearrowright X$, define $\varphi(g)(x) = g \cdot x$. Then $\varphi(g)$ is a bijection $X \to X$, and $\varphi(gh) = \varphi(g) \circ \varphi(h)$.

</v-click>

<v-click>

**Homomorphism $\to$ action:** Given $\varphi: G \to \operatorname{Sym}(X)$, define $g \cdot x = \varphi(g)(x)$.

</v-click>

<v-click>

| Property of action | Translates to |
|-------------------|---------------|
| **Faithful** (only $e$ fixes all $x$) | $\varphi$ is **injective** ($G \hookrightarrow \operatorname{Sym}(X)$) |
| **Trivial** ($g \cdot x = x$ always) | $\varphi$ is the **zero map** |
| **Kernel** of the action | $\ker(\varphi) = \{g \mid g \cdot x = x\; \forall x\}$ |

</v-click>

<v-click>

**Cayley's Theorem.** Every group $G$ embeds into $\operatorname{Sym}(G)$ via the left-multiplication action. So every group is isomorphic to a subgroup of some symmetric group.

</v-click>

---

# Discrete Examples I: Symmetry of Polygons

**Example 1.** The dihedral group $D_n$ acts on the vertices of a regular $n$-gon.

<img src="/d7-symmetry.png" style="height: 180px; margin-top: 0.3rem;" />

<v-click>

$D_7$ has $2 \times 7 = 14$ elements: 7 rotations ($e, r, r^2, \ldots, r^6$) and 7 reflections.

Each symmetry permutes the 7 vertices $\implies$ $D_7 \hookrightarrow S_7$.

</v-click>

<v-click>

**Example 2.** The **Rubik's cube group** acts on the 54 colored facelets. It is a subgroup of $S_{54}$ with $|G| \approx 4.3 \times 10^{19}$.

</v-click>

---

# Discrete Examples: Rubik's Cube as a Group Action

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 0.92rem;">

The 6 face rotations $S = \{U, D, L, R, F, B\}$ generate the **Rubik's cube group** $G = \langle S \rangle \leq S_{48}$ (permutations of 48 movable facelets).

<v-click>

**Configurations as an orbit**: $G$ acts on the set of configurations $\mathcal{C}$ (all reachable states from solved). The stabilizer of the solved state is $G_{c_0} = \{e\}$ (the action on facelets is **faithful** — only the identity fixes all 48). By orbit-stabilizer:
$$|\mathcal{C}| = [G : G_{c_0}] = |G| \approx 4.3 \times 10^{19}$$

</v-click>

<v-click>

**$G$ acts on facelets**: each $g \in G$ permutes the 48 facelets. Orbits: 24 corner facelets (8 cubies $\times$ 3 faces) and 24 edge facelets (12 cubies $\times$ 2 faces) — **not transitive**.

</v-click>

<v-click>

**God's number** = 20 = diameter of the Cayley graph $\operatorname{Cay}(G, S^{\pm})$: every $g \in G$ is a product of $\leq 20$ generators (Rokicki et al., 2010).

</v-click>

</div>
<div style="flex: 0 0 auto;">

<img src="/rubik.jpg" style="height: 200px; border-radius: 4px;" />

</div>
</div>

---

# Rubik's Cube: Structure and Order

The cube has **8 corner cubies** (3 orientations each) and **12 edge cubies** (2 orientations each).

<v-click>

Without constraints, all rearrangements would give:
$$|S_8| \cdot 3^8 \cdot |S_{12}| \cdot 2^{12} = 8!\cdot 3^8 \cdot 12!\cdot 2^{12}$$

</v-click>

<v-click>

But **3 constraints** reduce this by a factor of $12$:
1. Corner and edge permutations have **same parity** ($\div 2$)
2. Total corner twist $\equiv 0 \pmod{3}$ ($\div 3$)
3. Total edge flip $\equiv 0 \pmod{2}$ ($\div 2$)

</v-click>

<v-click>

$$|G| = \frac{8!\cdot 3^8 \cdot 12!\cdot 2^{12}}{12} = 43{,}252{,}003{,}274{,}489{,}856{,}000$$

</v-click>

<v-click>

**Exercise.** Verify constraint 1: show that every face rotation is an **even** permutation of both corners and edges. *(Hint: a 4-cycle is odd, but each face move is a product of two 4-cycles.)*

*Ref: Joyner, Adventures in Group Theory (2008); Rokicki et al., "God's Number is 20" (2010).*

</v-click>

---

# Discrete Examples II: Conjugation

**Example 3.** Any group $G$ acts on **itself** by conjugation:
$$g \cdot x = gxg^{-1}$$

<v-click>

- **Orbit** of $x$ = **conjugacy class** $\operatorname{Cl}(x) = \{gxg^{-1} \mid g \in G\}$

</v-click>

<v-click>

- **Stabilizer** of $x$ = **centralizer** $C_G(x) = \{g \in G \mid gx = xg\}$

</v-click>

<v-click>

- **Fixed points** = **center** $Z(G) = \{x \in G \mid gx = xg \text{ for all } g\}$

</v-click>

<v-click>

This action is the key tool for Sylow theorems (next lectures).

</v-click>

---

# Discrete Examples III: Action on Cosets

**Example 4.** $G$ acts on the coset space $G/H$ by left multiplication:
$$g \cdot (aH) = (ga)H$$

<v-click>

This is always a **transitive** action (only one orbit).

</v-click>

<v-click>

**Stabilizer** of the coset $eH$: $G_{eH} = H$.

</v-click>

<v-click>

**Example 5.** $S_n$ acts on polynomials by permuting variables:
$$\sigma \cdot f(x_1, \ldots, x_n) = f(x_{\sigma(1)}, \ldots, x_{\sigma(n)})$$

The **fixed points** are the **symmetric polynomials** (e.g., $e_1 = \sum x_i$, $e_2 = \sum_{i<j} x_i x_j$).

</v-click>

---

# Orbits

**Definition.** The **orbit** of $x \in X$ under $G$ is:
$$G \cdot x = \{g \cdot x \mid g \in G\}$$

<v-click>

**Theorem.** The orbits partition $X$:
$$X = G \cdot x_1 \sqcup G \cdot x_2 \sqcup \cdots \sqcup G \cdot x_k$$

</v-click>

<v-click>

*Proof.* Define $x \sim y \iff \exists\, g \in G,\, g \cdot x = y$. This is an equivalence relation:
- Reflexive: $e \cdot x = x$
- Symmetric: $g \cdot x = y \implies g^{-1} \cdot y = x$
- Transitive: $g \cdot x = y,\, h \cdot y = z \implies (hg) \cdot x = z$ $\square$

</v-click>

---

# Stabilizers

**Definition.** The **stabilizer** (or **isotropy group**) of $x \in X$ is:
$$G_x = \{g \in G \mid g \cdot x = x\}$$

<v-click>

**Proposition.** $G_x \leq G$ (it is a subgroup).

*Proof.* (i) $e \cdot x = x$, so $e \in G_x$. (ii) If $g, h \in G_x$, then $(gh) \cdot x = g \cdot (h \cdot x) = g \cdot x = x$. (iii) If $g \in G_x$, then $g^{-1} \cdot x = g^{-1} \cdot (g \cdot x) = (g^{-1}g) \cdot x = x$. $\square$

</v-click>

<v-click>

| Action | Stabilizer of $x$ | Name |
|--------|-------------------|------|
| Conjugation on $G$ | $C_G(x)$ | centralizer |
| Left mult. on $G/H$ | $H$ | the subgroup itself |
| $SO(3)$ on $S^2$ | rotations fixing $x$ $\cong SO(2)$ | — |

</v-click>

---

# The Orbit-Stabilizer Theorem

**Theorem.** If $G$ acts on $X$ and $x \in X$, then
$$|G \cdot x| = [G : G_x] = \frac{|G|}{|G_x|}$$

<v-click>

*Proof sketch.* The map $gG_x \mapsto g \cdot x$ is a well-defined bijection from $G/G_x$ to $G \cdot x$.

</v-click>

<v-click>

**Example:** $D_4$ acts on vertices of a square.
- Orbit of vertex $1$ = all 4 vertices (transitive), so $|G \cdot 1| = 4$
- $|D_4| = 8$, so $|G_1| = 8/4 = 2$
- Indeed, $G_1 = \{e, s\}$ where $s$ is the reflection fixing vertex 1

</v-click>

<v-click>

**Corollary.** If $G$ is finite and acts on $X$, then $|G \cdot x|$ divides $|G|$.

</v-click>

---

# The Class Equation

Apply conjugation action $G \curvearrowright G$ with $g \cdot x = gxg^{-1}$:

<v-click>

$$|G| = |Z(G)| + \sum_{i} [G : C_G(x_i)]$$

where the sum runs over representatives of non-central conjugacy classes.

</v-click>

<v-click>

**Example:** $S_3$ has order 6, center $Z(S_3) = \{e\}$.

| Conjugacy class | Size | $[G:C_G(x)]$ |
|----------------|------|---------------|
| $\{e\}$ | 1 | (center) |
| $\{(12),(13),(23)\}$ | 3 | $6/2 = 3$ |
| $\{(123),(132)\}$ | 2 | $6/3 = 2$ |

Check: $6 = 1 + 3 + 2$ $\checkmark$

</v-click>

---

# Burnside's Lemma

**Theorem** (Burnside / Cauchy–Frobenius). The number of orbits of $G$ acting on $X$ is:
$$|X/G| = \frac{1}{|G|} \sum_{g \in G} |X^g|$$

where $X^g = \{x \in X \mid g \cdot x = x\}$ is the set of fixed points of $g$.

<v-click>

*"Count equals the average number of fixed points."*

</v-click>

<v-click>

**Q: How many distinct ways to color the vertices of a square with 2 colors, up to rotation?**

<img src="/burnside-square.png" style="height: 100px; margin-top: 0.3rem;" />

</v-click>

---

# Burnside: Square Coloring

$D_4 = \{e, r, r^2, r^3, s, rs, r^2s, r^3s\}$ acts on $2^4 = 16$ colorings.

**Count fixed points for each element:**

| $g$ | $|X^g|$ | Why? |
|-----|---------|------|
| $e$ | 16 | all colorings fixed |
| $r, r^3$ | 2 each | all vertices same color |
| $r^2$ | 4 | opposite pairs same |
| $s, r^2s$ | 8 each | reflection axis fixes pairs |
| $rs, r^3s$ | 4 each | diagonal reflection |

<v-click>

$$|X/G| = \frac{1}{8}(16 + 2 + 4 + 2 + 8 + 4 + 8 + 4) = \frac{48}{8} = 6$$

</v-click>

---

# Platonic Solids: Symmetry as Group Action

The symmetry group of a solid acts on its vertices, edges, and faces.

<img src="/platonic-solids.png" style="height: 200px; margin: 0.3rem 0;" />

<v-click>

| Solid | Vertices | Rotation group | Full symmetry | Order |
|-------|----------|---------------|---------------|-------|
| Tetrahedron | 4 | $A_4$ | $S_4$ | 24 |
| Cube / Octahedron | 8 / 6 | $S_4$ | $S_4 \times C_2$ | 48 |
| Icosahedron / Dodecahedron | 12 / 20 | $A_5$ | $A_5 \times C_2$ | 120 |

</v-click>

<v-click>

**Dual pairs** (cube $\leftrightarrow$ octahedron, icosahedron $\leftrightarrow$ dodecahedron) have the **same** symmetry group — because the dual exchanges vertices and faces.

</v-click>

---

# Platonic Solids: Orbit-Stabilizer in Action

<div style="font-size: 0.95rem;">

**Example:** Compute $|SO|$ (rotation group of the cube) using orbit-stabilizer.

<v-click>

$SO$ acts on the 8 vertices of the cube. Pick a vertex $v$:
- **Orbit**: $SO$ acts transitively $\implies |SO \cdot v| = 8$
- **Stabilizer**: rotations fixing $v$ = rotations about the diagonal through $v$ $\implies |G_v| = 3$
- **Orbit-stabilizer**: $|SO| = |SO \cdot v| \cdot |G_v| = 8 \times 3 = 24$

</v-click>

<v-click>

The full symmetry group includes reflections: $O = SO \cup s \cdot SO$, so $|O| = 48$.

</v-click>

<v-click>

**Connection to reflection groups**: each full symmetry group $T, O, I$ is a **finite reflection group** (Coxeter group), generated by reflections in $\mathbb{R}^3$. These are exactly the 3D irreducible types: $A_3, B_3, H_3$.

$A_5 \cong SI$ is the smallest **non-abelian simple group** — this connects to the **insolvability of the quintic** via Galois theory (Lecture 24).

</v-click>

</div>

---

# Continuous Examples I: Rotations

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1;">

**Example 6.** $SO(3)$ acts on $S^2$ — **transitively** (one orbit = entire sphere).

<v-click>

- **Stabilizer** of north pole $= SO(2)$ (rotations about $z$-axis)
- Orbit-stabilizer: $S^2 \cong SO(3)/SO(2)$

</v-click>

<v-click>

The subgroup $SO(2) \leq SO(3)$ acts on $S^2$ **non-transitively**: orbits = latitude circles, poles are fixed points.

</v-click>

<v-click>

**Example 7.** $O(n) \curvearrowright \mathbb{R}^n$ (orthogonal transformations).
- **Orbits** = concentric spheres $S^{n-1}_r$ (not transitive on $\mathbb{R}^n$!)
- **Stabilizer** of $(r,0,...,0)$ $\cong O(n-1)$

</v-click>

</div>
<div style="flex: 0 0 auto;">

<img src="/so3-sphere.png" style="height: 250px;" />

</div>
</div>

---

# Continuous Examples II: Linear and Modular

**Example 8.** $GL_n(\mathbb{R})$ acts on $\mathbb{R}^n$ by matrix multiplication: $A \cdot v = Av$.

<v-click>

- **Orbits**: $\{0\}$ and $\mathbb{R}^n \setminus \{0\}$ (any nonzero vector maps to any other)
- **Stabilizer** of $e_1 = (1,0,...,0)^T$: matrices with first column $e_1$

</v-click>

<v-click>

**Example 9.** $SL_2(\mathbb{Z})$ acts on the upper half-plane $\mathbb{H}$ (from Lecture 1):

$$\begin{pmatrix} a & b \\ c & d \end{pmatrix} \cdot z = \frac{az + b}{cz + d}$$

- **Orbit space** $\mathbb{H} / SL_2(\mathbb{Z})$ = modular curve (parameterizes elliptic curves)
- **Stabilizer** of $z = i$: $\left\{\pm\begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}, \pm I\right\} \cong \mathbb{Z}/2\mathbb{Z}$

</v-click>

---

# Application: Center of a $p$-Group

**Theorem.** If $|G| = p^n$ with $p$ prime and $n \geq 1$, then $Z(G) \neq \{e\}$.

<v-click>

*Proof.* Apply the **class equation**:
$$|G| = |Z(G)| + \sum_{i} [G : C_G(x_i)]$$

</v-click>

<v-click>

Each $[G:C_G(x_i)]$ divides $|G| = p^n$ and is $> 1$, so $p \mid [G:C_G(x_i)]$.

</v-click>

<v-click>

Therefore $p \mid |G| - \sum [G:C_G(x_i)] = |Z(G)|$.

Since $e \in Z(G)$, we have $|Z(G)| \geq p > 1$. $\square$

</v-click>

<v-click>

**Corollary.** Groups of order $p^2$ are abelian. *(Hint: if $G/Z(G)$ is cyclic, then $G$ is abelian.)*

This result will be crucial for Sylow theory (Lectures 3–4).

</v-click>

---

# Exercises

**Exercise 1.** Let $G = D_3$ (symmetries of an equilateral triangle). List all orbits and stabilizers for the action on the 3 vertices.

**Exercise 2.** Compute the number of distinct necklaces with 6 beads of 2 colors, up to rotation. *(Use Burnside with $\mathbb{Z}/6\mathbb{Z}$.)*

**Exercise 3.** Let $G$ act on itself by conjugation. Show that the orbit of $x$ has size 1 if and only if $x \in Z(G)$.

**Exercise 4.** Prove: if $G$ acts transitively on $X$ and $|X| > 1$, then some $g \in G$ has no fixed points.

**Exercise 5.** Show that $O(n)$ acts on the set of symmetric $n \times n$ matrices by $A \cdot S = ASA^T$. What are the orbits?

**Exercise 6.** Use the class equation to show: if $|G| = p^2$, then $G$ is abelian.

---

# Looking Ahead

We now have the tools for **Sylow theory**:

<v-click>

- **Lecture 3**: Cauchy's theorem (via group action on tuples) and the normalizer lemma

</v-click>

<v-click>

- **Lecture 4**: Sylow I (existence), Sylow II (conjugacy), Sylow III (counting)

</v-click>

<v-click>

The key idea: choose the right group action on the right set, then count.

**"Group actions are the single most important tool in finite group theory."**

</v-click>

---
layout: center
---

# Questions?
