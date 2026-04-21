---
title: "MAT205: Abstract Algebra II — Lecture 4"
math: katex
---

# MAT205: Abstract Algebra II

## 4. Applications of the Sylow Theorems

<br/>

**Ma, Jia-Jun** — Xiamen University Malaysia

---

# From Existence to Structure

In Lecture 3, Sylow theory told us:

<v-click>

- when $p$-subgroups **exist**
- how many Sylow $p$-subgroups there can be
- when a Sylow subgroup must be **normal**

</v-click>

<v-click>

Today we use Sylow theory in the most important way:

$$\boxed{\text{to determine the structure of a finite group}}$$

</v-click>

<v-click>

Our main example:

$$|G| = 21 = 3 \cdot 7$$

</v-click>

---

# Appetizer: Groups of Order $pq$ are Not Simple

**Theorem.** Let $p < q$ be primes. Any group $G$ with $|G| = pq$ has a normal Sylow $q$-subgroup. In particular, $G$ is **not simple**.

<v-click>

*Proof.* By Sylow III: $\;n_q \mid p$ and $n_q \equiv 1 \pmod q$.

</v-click>

<v-click>

Since $p$ is prime, $n_q \in \{1, p\}$.

If $n_q = p$, then $p \equiv 1 \pmod q$, i.e., $q \mid (p-1)$, so $p \geq q + 1 > q$ — contradicting $p < q$.

Hence $n_q = 1$, and the unique Sylow $q$-subgroup is normal. $\square$

</v-click>

<v-click>

**Examples:**
- $|G| = 15 = 3 \cdot 5$: $n_5 = 1$, in fact $G \cong \mathbb{Z}_{15}$ (unique up to iso).
- $|G| = 21 = 3 \cdot 7$: $n_7 = 1$, but there are **two** groups (see below!).
- $|G| = 35 = 5 \cdot 7$: $n_7 = 1$, $G \cong \mathbb{Z}_{35}$.

</v-click>

<v-click>

**Going deeper:** what is the full classification? This is what we'll do for $|G| = 21$.

</v-click>

---

# Sylow Analysis of $|G| = 21$

Let $G$ be a group of order $21 = 3 \cdot 7$. Apply Sylow III to both primes:

<v-click>

**Sylow 7-subgroup** $P$: $\;n_7 \mid 3$ and $n_7 \equiv 1 \pmod 7$.

Only $n_7 = 1$ works, so $P \trianglelefteq G$ and $P \cong \mathbb{Z}_7$.

</v-click>

<v-click>

**Sylow 3-subgroup** $Q$: $\;n_3 \mid 7$ and $n_3 \equiv 1 \pmod 3$.

Both $n_3 = 1$ and $n_3 = 7$ satisfy these, so $n_3 \in \{1, 7\}$. Either way, $Q \cong \mathbb{Z}_3$.

</v-click>

<v-click>

**Two cases to analyze:**

| Case | $n_3$ | Is $Q$ normal? |
|------|-------|---------------|
| 1 | 1 | yes $\Rightarrow$ $G$ is a direct product |
| 2 | 7 | no $\Rightarrow$ need a new construction |

</v-click>

---

# Interlude: The Product Set $PQ$

**Definition.** For subgroups $P, Q \leq G$:
$$PQ = \{pq \mid p \in P,\; q \in Q\} \subseteq G$$

<v-click>

**Warning:** $PQ$ is a **subset**, not always a subgroup!

</v-click>

<v-click>

**Lemma.** $PQ$ is a subgroup $\iff PQ = QP$.

*Sufficient condition:* If $P \subseteq N_G(Q)$ or $Q \subseteq N_G(P)$, then $PQ = QP$ (hence $PQ \leq G$).

</v-click>

<v-click>

*Proof of sufficient condition.* If $P \subseteq N_G(Q)$, then $pQp^{-1} = Q$, so $pQ = Qp$ for every $p \in P$. Hence $PQ = \bigcup_p pQ = \bigcup_p Qp = QP$. $\square$

</v-click>

---

# The Size Formula for $PQ$

<div style="font-size: 0.9rem;">

**Theorem.** For any subgroups $P, Q \leq G$ (even if $PQ$ is not a subgroup):
$$|PQ| = \frac{|P| \cdot |Q|}{|P \cap Q|}$$

<v-click>

*Proof via group action.* Let $P \times Q$ act on $G$ by $(p, q) \cdot g = p\, g\, q^{-1}$.

</v-click>

<v-click>

**Orbit of $e$:** $\;(P \times Q) \cdot e = \{p q^{-1} \mid p \in P, q \in Q\} = PQ$ (using $Q^{-1} = Q$).

</v-click>

<v-click>

**Stabilizer of $e$:** $\;(p, q) \in \mathrm{Stab}(e) \iff p e q^{-1} = e \iff p = q \in P \cap Q$. So
$$\mathrm{Stab}(e) = \{(x, x) \mid x \in P \cap Q\} \cong P \cap Q$$

</v-click>

<v-click>

**Orbit-stabilizer:**
$$|PQ| = |(P \times Q) \cdot e| = \frac{|P \times Q|}{|\mathrm{Stab}(e)|} = \frac{|P| \cdot |Q|}{|P \cap Q|} \qquad\square$$

</v-click>

</div>

---

# When is $PQ \cong P \times Q$?

**Proposition.** Let $P, Q \leq G$. If:

- $P \subseteq N_G(Q)$ and $Q \subseteq N_G(P)$ (each normalizes the other),
- $P \cap Q = \{e\}$,

then $PQ$ is a subgroup and $PQ \cong P \times Q$.

<v-click>

*Proof.* Both normalizers $\Rightarrow PQ$ is a subgroup (by previous lemma).

For any $p \in P, q \in Q$: the commutator $[p, q] = pqp^{-1}q^{-1}$ lies in $P \cap Q$:
- $pqp^{-1} \in Q$ since $P \subseteq N_G(Q)$, so $[p,q] = (pqp^{-1})q^{-1} \in Q$
- $qp^{-1}q^{-1} \in P$ since $Q \subseteq N_G(P)$, so $[p,q] = p(qp^{-1}q^{-1}) \in P$

</v-click>

<v-click>

Hence $[p,q] \in P \cap Q = \{e\}$, i.e., $pq = qp$ — elements of $P$ and $Q$ commute.

The map $P \times Q \to PQ$, $(p, q) \mapsto pq$, is a homomorphism, surjective, with trivial kernel. $\square$

</v-click>

---

# Case 1: $n_3 = 1$ — Both Sylow Subgroups Normal

Both $P, Q \trianglelefteq G$, $P \cap Q = \{e\}$ (coprime orders). Applying the proposition:
- $P \trianglelefteq G \Rightarrow Q \subseteq G = N_G(P)$ ✓
- $Q \trianglelefteq G \Rightarrow P \subseteq G = N_G(Q)$ ✓

<v-click>

So $PQ \cong P \times Q$, and $|PQ| = 21 = |G|$, hence $G = PQ$:
$$G \cong \mathbb{Z}_7 \times \mathbb{Z}_3 \cong \mathbb{Z}_{21}$$

</v-click>

<v-click>

**Case 2** ($n_3 = 7$): $Q$ is not normal — $G$ is **not** a direct product. But $P \trianglelefteq G$ still means $Q$ acts on $P$ by conjugation:

$$G = \text{``}\mathbb{Z}_7 \text{ with a } \mathbb{Z}_3\text{-action''} \quad \longrightarrow \quad \text{semidirect product}$$

To handle this case we first develop the theory of semidirect products.

</v-click>

---

# A Motivating Example: $S_3$

Consider the smallest non-abelian group $S_3$ (order 6).

<v-click>

Inside $S_3$:
- $N = A_3 = \langle (123) \rangle \cong \mathbb{Z}_3$, with $N \trianglelefteq S_3$
- $H = \langle (12) \rangle \cong \mathbb{Z}_2$, a subgroup (not normal!)

</v-click>

<v-click>

**Observation:** $N \cap H = \{e\}$ and $|N| \cdot |H| = 6 = |S_3|$, so $S_3 = NH$ (every element $\sigma = \nu h$ uniquely).

</v-click>

<v-click>

This looks just like a direct product! But $S_3 \not\cong \mathbb{Z}_3 \times \mathbb{Z}_2 = \mathbb{Z}_6$ — $S_3$ is non-abelian.

$$\text{Something subtle is happening.}$$

</v-click>

---

# Why $S_3$ Is Not $\mathbb{Z}_6$

Both $S_3$ and $\mathbb{Z}_6$ contain a subgroup $\mathbb{Z}_3$ and a subgroup $\mathbb{Z}_2$, both with trivial intersection. The **multiplication rule differs**:

<v-click>

In $\mathbb{Z}_6 = \mathbb{Z}_3 \times \mathbb{Z}_2$: elements of $\mathbb{Z}_3$ and $\mathbb{Z}_2$ **commute**.

</v-click>

<v-click>

In $S_3$: let $r = (123) \in N$, $s = (12) \in H$. Compute:
$$s r s^{-1} = (12)(123)(12) = (132) = r^{-1}$$

So $s$ **conjugates** $r$ to $r^{-1}$ — $H$ acts **nontrivially** on $N$ by automorphisms.

</v-click>

<v-click>

**Key insight:** $S_3$ is not just $N$ and $H$ sitting side by side — $H$ **acts on** $N$ by conjugation, twisting the multiplication.

This twisting is exactly what a **semidirect product** captures — we make this precise next.

</v-click>

---

# Group Extensions: Building Bigger Groups

<div style="font-size: 0.92rem;">

A **short exact sequence** of groups:
$$1 \to K \xrightarrow{\iota} G \xrightarrow{\pi} H \to 1$$

<v-click>

means $\iota$ injective, $\pi$ surjective, and $\operatorname{im}(\iota) = \ker(\pi)$ — equivalently:
$$K \trianglelefteq G \quad \text{and} \quad G/K \cong H$$

We say $G$ is an **extension** of $H$ by $K$.

</v-click>

<v-click>

**Structural interpretation:**
- $K$ is a **normal subgroup** of $G$ (the "kernel piece")
- $H \cong G/K$ is the **quotient** (the "external piece")
- $|G| = |K| \cdot |H|$

</v-click>

<v-click>

**Extension problem:** given $K$ and $H$, classify all $G$ fitting into such a sequence — inverse of forming quotients, **has many solutions** in general.

</v-click>

</div>

---

# Not Every Extension Splits

**Simplest example:** $\;1 \to \mathbb{Z}_2 \to \mathbb{Z}_4 \to \mathbb{Z}_2 \to 1$

<v-click>

- $\mathbb{Z}_2 \cong \{0, 2\} \trianglelefteq \mathbb{Z}_4$ (the unique order-2 subgroup)
- $\mathbb{Z}_4 / \{0, 2\} \cong \mathbb{Z}_2$
- So $\mathbb{Z}_4$ is an extension of $\mathbb{Z}_2$ by $\mathbb{Z}_2$.

</v-click>

<v-click>

**Does it split?** We'd need a subgroup $H \leq \mathbb{Z}_4$ with $|H| = 2$ and $H \cap \{0,2\} = \{0\}$. But $\{0, 2\}$ is the **only** order-2 subgroup of $\mathbb{Z}_4$! So no complement exists.

</v-click>

<v-click>

**Consequence:** $\mathbb{Z}_4 \not\cong \mathbb{Z}_2 \rtimes \mathbb{Z}_2$. In fact the only order-4 semidirect products are $\mathbb{Z}_2 \times \mathbb{Z}_2$ (trivial action, since $\operatorname{Aut}(\mathbb{Z}_2) = 1$).

The cyclic group $\mathbb{Z}_4$ is **genuinely a non-trivial extension** — it doesn't factor as a semidirect product.

</v-click>

<v-click>

**Moral:** extensions are more general than semidirect products. The classification of non-split extensions leads to **group cohomology** $H^2(H; K)$ — a topic for later.

</v-click>

---

# Semidirect Product: Definition

**Data:** groups $K, H$ and a homomorphism $\varphi : H \to \operatorname{Aut}(K)$ — an **action of $H$ on $K$ by automorphisms**.

<v-click>

**Definition.** $K \rtimes_\varphi H$ is the set $K \times H$ with multiplication
$$(k_1, h_1)(k_2, h_2) = \bigl(k_1 \cdot \varphi(h_1)(k_2),\; h_1 h_2\bigr)$$

The second factor multiplies as usual; $\varphi(h_1)$ **twists** the first factor.

</v-click>

<v-click>

**Special case.** If $\varphi$ is trivial: $K \rtimes_\varphi H = K \times H$ (direct product).

</v-click>

<v-click>

**As an extension:** $K \rtimes_\varphi H$ fits into the split exact sequence
$$1 \to K \to K \rtimes_\varphi H \to H \to 1$$
with splitting $h \mapsto (e_K, h)$.

</v-click>

---

# Internal vs External

**External:** start with $\varphi: H \to \operatorname{Aut}(K)$, build $K \rtimes_\varphi H$ on $K \times H$.

**Internal:** inside a group $G$, if $N \trianglelefteq G$, $H \leq G$, $N \cap H = \{e\}$, $NH = G$, then
$$G \cong N \rtimes_\varphi H, \qquad \varphi(h)(n) = h n h^{-1}$$

<v-click>

**These are the same thing:**
- Internal $\Rightarrow$ External: conjugation gives the action $\varphi$.
- External $\Rightarrow$ Internal: the copies $K \times \{e\}$ and $\{e\} \times H$ satisfy the internal conditions.

</v-click>

<v-click>

**Three equivalent viewpoints:**

<div style="font-size: 0.9rem;">

$$\underbrace{\text{split exact sequence}}_{\text{extension}} \;\;\Longleftrightarrow\;\; \underbrace{N \trianglelefteq G,\; N \cap H = 1,\; NH = G}_{\text{subgroup}} \;\;\Longleftrightarrow\;\; \underbrace{\varphi : H \to \operatorname{Aut}(N)}_{\text{action}}$$

</div>

</v-click>

---

# Discrete Example: The Dihedral Group

The dihedral group $D_n$ (symmetry group of regular $n$-gon) has presentation
$$D_n = \langle r,s \mid r^n = e,\; s^2 = e,\; srs^{-1} = r^{-1} \rangle$$

<v-click>

- $\langle r \rangle \cong \mathbb{Z}_n$ is the rotation subgroup (normal)
- $\langle s \rangle \cong \mathbb{Z}_2$ is generated by a reflection

</v-click>

<v-click>

Conjugation by $s$ acts on $\langle r \rangle$ by $r \mapsto r^{-1}$, so:

$$\boxed{D_n \cong \mathbb{Z}_n \rtimes \mathbb{Z}_2}$$

where $\mathbb{Z}_2$ acts on $\mathbb{Z}_n$ by **inversion**.

</v-click>

---

# Continuous Example: Rigid Motions of $\mathbb{R}^3$

$SO(3)$ acts on $(\mathbb{R}^3, +)$ by rotations ($A \cdot v = Av$), giving a homomorphism $SO(3) \to \operatorname{Aut}(\mathbb{R}^3, +)$.

<v-click>

The semidirect product
$$\boxed{\mathbb{R}^3 \rtimes SO(3)}$$
is the group of **orientation-preserving rigid motions** of Euclidean 3-space (rotations + translations).

</v-click>

<v-click>

An element $(v, A)$ means: first rotate by $A$, then translate by $v$. Multiplication:
$$(v, A)(w, B) = (v + Aw,\; AB)$$

</v-click>

<v-click>

**Physics:** this is the special Euclidean group $SE(3)$ — describes rigid body motion, used in robotics, mechanics, and computer graphics.

</v-click>

---

# Automorphisms of Cyclic Groups

**Theorem.** $\;\operatorname{Aut}(\mathbb{Z}_n) \cong (\mathbb{Z}/n\mathbb{Z})^\times$, the group of units mod $n$.

<v-click>

*Proof.* Every $\sigma \in \operatorname{Aut}(\mathbb{Z}_n)$ is determined by $\sigma(1) \in \mathbb{Z}_n$. For $\sigma$ to be an automorphism, $\sigma(1)$ must generate $\mathbb{Z}_n$, i.e., $\gcd(\sigma(1), n) = 1$.

The map $\sigma \mapsto \sigma(1)$ gives an isomorphism $\operatorname{Aut}(\mathbb{Z}_n) \cong (\mathbb{Z}/n\mathbb{Z})^\times$. $\square$

</v-click>

<v-click>

**Corollary.** $\;|\operatorname{Aut}(\mathbb{Z}_n)| = \#\{k \in \{1, \ldots, n\} \mid \gcd(k,n) = 1\}$ (Euler's totient).

</v-click>

<v-click>

**Special case.** For prime $p$: $\;\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$ is a field, and
$$\operatorname{Aut}(\mathbb{Z}_p) \cong \mathbb{F}_p^\times \cong \mathbb{Z}_{p-1}$$

**Theorem** *(to be proved in Part II)*. Any finite subgroup of the multiplicative group of a field is **cyclic**.

</v-click>

---

# Back to $|G| = 21$: Compute $\operatorname{Aut}(\mathbb{Z}_7)$

<div style="font-size: 0.9rem;">

Apply the theorem with $p = 7$: $\;\operatorname{Aut}(\mathbb{Z}_7) \cong (\mathbb{Z}/7\mathbb{Z})^\times$, cyclic of order 6.

The isomorphism $(\mathbb{Z}/7\mathbb{Z})^\times \cong \mathbb{Z}_6$ **depends on a choice of generator**.

<v-click>

**Orders in $(\mathbb{Z}/7\mathbb{Z})^\times$:**

| $k$ | 1 | 2 | 3 | 4 | 5 | 6 |
|-----|---|---|---|---|---|---|
| $\operatorname{ord}(k)$ | 1 | 3 | **6** | 3 | **6** | 2 |

$2^3 = 8 \equiv 1 \pmod 7$, so $\operatorname{ord}(2) = 3$ — **2 is not a generator**.

</v-click>

<v-click>

**Verify $3$ is a generator:**
$$3^1 \equiv 3,\;\; 3^2 \equiv 2,\;\; 3^3 \equiv 6,\;\; 3^4 \equiv 4,\;\; 3^5 \equiv 5,\;\; 3^6 \equiv 1 \pmod 7$$

Hence $(\mathbb{Z}/7\mathbb{Z})^\times = \langle 3 \rangle$, and we seek $\;\varphi : \mathbb{Z}_3 \to \operatorname{Aut}(\mathbb{Z}_7) \cong \mathbb{Z}_6$.

</v-click>

</div>

---

# Classification: Two Groups of Order 21

Homomorphisms $\varphi : \mathbb{Z}_3 \to \mathbb{Z}_6$ are determined by where the generator goes, and $\mathbb{Z}_6$ has exactly $\gcd(3,6) = 3$ solutions, giving **two isomorphism classes** of $\varphi$: trivial or nontrivial.

<v-click>

**Case 1** (trivial $\varphi$): $\;G \cong \mathbb{Z}_7 \times \mathbb{Z}_3 \cong \mathbb{Z}_{21}$ — the cyclic group.

</v-click>

<v-click>

**Case 2** (nontrivial $\varphi$): $\;\mathbb{Z}_3$ acts via an order-3 automorphism of $\mathbb{Z}_7$. Since $\operatorname{ord}(2) = 3$ in $(\mathbb{Z}/7\mathbb{Z})^\times$, we can take $\varphi(1): a \mapsto a^2$. This gives the non-abelian group with presentation:

$$G = \langle a, b \mid a^7 = e,\; b^3 = e,\; bab^{-1} = a^2 \rangle \;\cong\; \mathbb{Z}_7 \rtimes \mathbb{Z}_3$$

</v-click>

<v-click>

$$\boxed{\text{Up to isomorphism, there are exactly two groups of order 21.}}$$

</v-click>

<v-click>

**The Sylow workflow:**
1. Sylow III forces a normal subgroup $P$
2. $P$ gives a decomposition $G \cong P \rtimes_\varphi H$
3. Automorphisms $H \to \operatorname{Aut}(P)$ classify the possibilities

This is the **standard recipe** for classifying groups of small order.

</v-click>

---

# Example: $|G| = 36$ is Not Simple

<div style="font-size: 0.9rem;">

**Theorem.** No group of order $36$ is simple.

<v-click>

$|G| = 36 = 2^2 \cdot 3^2$. By Sylow III: $n_3 \mid 4$ and $n_3 \equiv 1 \pmod 3$, so $n_3 \in \{1, 4\}$.

</v-click>

<v-click>

**Case 1** ($n_3 = 1$): the unique Sylow 3-subgroup is normal — done. $\checkmark$

</v-click>

<v-click>

**Case 2** ($n_3 = 4$): Let $G$ act on $\mathrm{Syl}_3(G) = \{P_1, P_2, P_3, P_4\}$ by conjugation, giving $\;\varphi : G \to S_4$.

- By Sylow II the action is **transitive**, so $\varphi$ is nontrivial.
- But $|G| = 36 > 24 = |S_4|$ forces $\varphi$ **not injective**.

So $\ker(\varphi)$ is a proper nontrivial normal subgroup of $G$. $\;\square$

</v-click>

<v-click>

**Concrete model** for Case 2: $\;G = A_4 \times \mathbb{Z}_3\;$ has order 36 with $n_3 = 4$.

Here $A_4 \hookrightarrow S_4$ gives $\varphi$, and $\;\ker(\varphi) = \{e\} \times \mathbb{Z}_3 \cong \mathbb{Z}_3$.

</v-click>

<v-click>

**Technique (pigeonhole):** if $|G| > n_p!$, then the conjugation action on $\mathrm{Syl}_p(G)$ gives a nontrivial kernel, so $G$ is not simple.

</v-click>

</div>

---

# Example: $|G| = 48$ is Not Simple (Fraleigh 37.13)

<div style="font-size: 0.82rem;">

**Theorem.** $G$ has a normal subgroup of order $8$ or $16$.

$|G| = 48 = 2^4 \cdot 3$. Sylow III: $n_2 \in \{1, 3\}$. **Case 1** ($n_2 = 1$): Sylow 2-subgroup is normal. $\checkmark$

<v-click>

**Case 2** ($n_2 = 3$): let $H, K$ be two distinct Sylow 2-subgroups ($|H|=|K|=16$). If $|H \cap K| \leq 4$, the size formula gives
$$|HK| = \frac{|H||K|}{|H \cap K|} \geq \frac{256}{4} = 64 > 48$$
— contradiction. So $|H \cap K| = 8$.

</v-click>

<v-click>

$[H : H \cap K] = 2 \Rightarrow H \cap K \trianglelefteq H$; similarly $\trianglelefteq K$. So $N_G(H \cap K) \supseteq H \cup K$, hence
$$|N_G(H \cap K)| \geq |HK| = \tfrac{16 \cdot 16}{8} = 32.$$

</v-click>

<v-click>

$|N_G(H \cap K)|$ divides 48 and is $\geq 32$ — the only such value is **48**. Hence $H \cap K \trianglelefteq G$, with $|H \cap K| = 8$. $\;\square$

</v-click>

<v-click>

**Faster (pigeonhole):** act on $\mathrm{Syl}_2(G)$ gives $\varphi: G \to S_3$; $|G| > |S_3|$ forces $|\ker \varphi| \geq 8$. — Weaker but quicker.

</v-click>

</div>

---

# How Small Can a Non-Abelian Simple Group Be?

We have seen that many small orders force a normal subgroup (by Sylow + counting). It is natural to ask:

$$\text{What is the smallest non-abelian simple group?}$$

<v-click>

**Theorem.** $\;A_5\;$ is simple, with $|A_5| = 60$.

No non-abelian simple group has order $< 60$ — this can be shown by Sylow case-by-case (see Fraleigh).

</v-click>

<v-click>

$A_5 \cong$ rotation group of the icosahedron/dodecahedron — will reappear in Part II for the **insolvability of the quintic**.

</v-click>

---

# Why $A_5$ is Simple: Proof Sketch

<div style="font-size: 0.85rem;">

**Strategy:** Any $N \trianglelefteq A_5$ is a union of conjugacy classes, contains $e$, and $|N| \mid 60$.

<v-click>

**Conjugacy classes of $A_5$:** $\;e\;$(1), 3-cycles (20), double transpositions (15), 5-cycles (12 + 12).

$$1 + 20 + 15 + 12 + 12 = 60 \; \checkmark$$

(In $S_5$ the 5-cycles form **one** class of size 24; in $A_5$ it **splits** into two of size 12.)

</v-click>

<v-click>

**Check divisibility:** $|N| = 1 + (\text{subset of } \{20, 15, 12, 12\})$.

Possible sums: $\;1,\, 13,\, 16,\, 21,\, 25,\, 28,\, 33,\, 36,\, 40,\, 45,\, 48,\, 60$.

Divisors of 60 in this list: only $\boxed{1 \text{ and } 60}$.

</v-click>

<v-click>

Hence $N = \{e\}$ or $N = A_5$. $\;\square$

</v-click>

</div>

---

# General Case: $A_n$ is Simple for $n \geq 5$

<div style="font-size: 0.85rem;">

**Theorem.** $A_n$ is simple for all $n \geq 5$.

<v-click>

*Proof sketch* — three key facts:

**(1) $A_n$ is generated by 3-cycles.**  Every even permutation is a product of an even number of transpositions, and $(ab)(cd) = (acb)(acd)$, $(ab)(ac) = (acb)$.

</v-click>

<v-click>

**(2) All 3-cycles are conjugate in $A_n$** (for $n \geq 5$).  In $S_n$ they're always conjugate via some $\pi$. If $\pi \notin A_n$, multiply by a transposition of two elements **not** moved by $\sigma$ — this requires $n \geq 5$.

</v-click>

<v-click>

**(3) Any nontrivial $N \trianglelefteq A_n$ contains a 3-cycle.**  Take $\sigma \in N \setminus \{e\}$ with fewest moved points. The commutator $\tau \sigma \tau^{-1} \sigma^{-1} \in N$ (for a well-chosen 3-cycle $\tau$) has strictly fewer moved points — unless $\sigma$ is already a 3-cycle.

</v-click>

<v-click>

Combining (2) + (3): $N$ contains one 3-cycle $\Rightarrow$ all 3-cycles $\Rightarrow$ $N = A_n$. $\;\square$

</v-click>

<v-click>

**Remark.** Fails for $n \leq 4$: $A_3 \cong \mathbb{Z}_3$ is abelian simple; $A_4$ has a normal Klein 4-subgroup — see next page for the geometric picture.

</v-click>

</div>

---

# Geometric View: Klein 4-Group in $A_4$

<div style="font-size: 0.85rem;">

$A_4 \cong$ rotation group of the regular tetrahedron ($12 =$ identity $+$ 8 vertex rotations $+$ 3 edge rotations).

<v-click>

The 6 edges form **3 pairs of opposite edges**; each pair determines an axis through the edge midpoints. The 180° rotations about these 3 axes give:

| Edge axis | 180° rotation |
|-----------|---------------|
| $\overline{12} \leftrightarrow \overline{34}$ | $(12)(34)$ |
| $\overline{13} \leftrightarrow \overline{24}$ | $(13)(24)$ |
| $\overline{14} \leftrightarrow \overline{23}$ | $(14)(23)$ |

These 3 rotations $+$ identity $= V_4 \trianglelefteq A_4$.

</v-click>

<v-click>

**Cube picture.** Inscribe the tetrahedron in a cube. The 3 edge-midpoint axes become the cube's 3 **coordinate axes** through opposite face centers.

</v-click>

<v-click>

**Why normal?** Conjugation permutes the 3 edge-axes (but preserves the set), so $V_4$ is invariant.

</v-click>

</div>

---

# Summary

For groups of order $21$:

<v-click>

- Sylow forces the subgroup of order $7$ to be normal
- this gives a decomposition
  $$G \cong \mathbb{Z}_7 \rtimes \mathbb{Z}_3$$
- the action is either trivial or nontrivial
- therefore there are exactly two groups of order $21$

</v-click>

<v-click>

And among all finite groups, the smallest non-abelian simple group is

$$A_5 \quad \text{of order} \quad 60.$$

</v-click>

---

# Homework (Lecture 4)

Fraleigh-inspired practice on applications of Sylow theory and semidirect products.

**Exercise 1.** Classify all groups of order $21$ up to isomorphism.

**Exercise 2.** Show that no group of order $20$ is simple.

**Exercise 3.** Show that no group of order $30$ is simple.

**Exercise 4.** Show that
$$S_3 \cong \mathbb{Z}_3 \rtimes \mathbb{Z}_2,$$
and identify explicitly the homomorphism
$$\mathbb{Z}_2 \to \operatorname{Aut}(\mathbb{Z}_3).$$
