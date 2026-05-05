---
title: "MAT205: Abstract Algebra II - Finite Simple Groups Through Three Examples"
math: katex
---

# MAT205: Abstract Algebra II

## Finite Simple Groups Through Three Examples

<br/>

**Ma, Jia-Jun** - Xiamen University Malaysia

---

# Goal

Lecture 8 ended with **composition factors**: every finite group breaks into
a list of finite simple groups. So every finite group is "made of" simple
groups.

<v-click>

This raises one natural question:

$$
\boxed{\text{Which finite simple groups are there?}}
$$

</v-click>

<v-click>

The full answer is the **Classification of Finite Simple Groups** (CFSG),
one of the deepest theorems of 20th-century mathematics. We will not prove
it. Instead, we **meet three concrete examples**, one from each kind of
family CFSG describes.

</v-click>

---

# Topics

<div style="font-size: 0.96rem;">

1. The landscape: what CFSG actually says.

2. **Example 1.** $\operatorname{PSL}_n(\mathbb F_p)$ — a classical Lie family.

3. **Example 2.** $M_{12}$ — a sporadic group, via Steiner systems.

4. **Example 3.** $G_2$ — an exceptional Lie family, via octonions.

5. Looking back at the landscape; bridges to the next chapters.

</div>

---

# Cast of Characters

<div style="font-size: 0.88rem;">

| Object | Role in this lecture |
|---|---|
| $\operatorname{PSL}_n(\mathbb F_p)$ | Example 1 — a classical Lie family |
| Steiner system $S(5,6,12)$ | the combinatorial object behind $M_{12}$ |
| $M_{12}$ | Example 2 — sporadic |
| Octonions $\mathbb O$ | the algebra behind $G_2$ |
| $G_2(\mathbb F_p)$ | Example 3 — exceptional Lie type over $\mathbb F_p$ |

</div>

---
layout: center
---

# Part I

## The Landscape of Finite Simple Groups

---

# Recall

A group $G$ is **simple** if its only normal subgroups are $\{1\}$ and $G$.

<v-click>

We have already met two infinite families of simple groups:

</v-click>

<v-click>

- L01: abelian simple groups are exactly $\mathbb Z_p$, $p$ prime.

</v-click>

<v-click>

- L04: $A_n$ is simple for $n\ge 5$.

</v-click>

<v-click>

Are there any others? The answer turns out to be: **yes, but only finitely
many more "kinds".**

</v-click>

---

# CFSG (≈ 2004)

**Theorem (Classification of Finite Simple Groups).** Every finite simple group
is one of:

<v-click>

1. cyclic of prime order;

</v-click>

<v-click>

2. alternating $A_n$, $n\ge 5$;

</v-click>

<v-click>

3. of **Lie type**, split into:
   - **classical**: $\operatorname{PSL}$, $\operatorname{PSU}$, $\operatorname{PSp}$, $\operatorname{P\Omega}^{\pm}$ over finite fields;
   - **exceptional**: $G_2$, $F_4$, $E_6$, $E_7$, $E_8$ and their twisted forms;

</v-click>

<v-click>

4. one of $26$ **sporadic** groups.

</v-click>

<v-click>

The proof spans roughly $10\,000$ pages. We will not enter it. Instead, the
rest of today is **three concrete examples**.

</v-click>

---

# Today's Three Examples

We already know the first two families ($\mathbb Z_p$, $A_n$). The remaining
two — Lie type and sporadic — are best learned by meeting examples.

<div style="font-size: 0.92rem;">

| Family | Today's example | Built from |
|---|---|---|
| classical Lie | $\operatorname{PSL}_n(\mathbb F_p)$ | linear algebra over $\mathbb F_p$ |
| sporadic | $M_{12}$ | a Steiner system $S(5,6,12)$ |
| exceptional Lie | $G_2(\mathbb F_p)$ | the octonion algebra $\mathbb O$ |

</div>

<v-click>

Each example is built from a different mathematical object. Together they
show how rich the answer to "which simple groups exist?" really is.

</v-click>

---
layout: center
---

# Part II

## Example 1 — $\operatorname{PSL}_n(\mathbb F_p)$ (classical Lie type)

---

# Linear Groups over $\mathbb F_p$

This first example you already know — we collect the orders in one place
before extending the pattern.

<v-click>

By counting ordered bases of $\mathbb F_p^n$:

$$
|\operatorname{GL}_n(\mathbb F_p)|=\prod_{i=0}^{n-1}(p^n-p^i).
$$

</v-click>

<v-click>

The determinant map $\operatorname{GL}_n\to\mathbb F_p^\times$ is surjective:

$$
|\operatorname{SL}_n(\mathbb F_p)|=\frac{|\operatorname{GL}_n(\mathbb F_p)|}{p-1}.
$$

</v-click>

<v-click>

$$
|\operatorname{PSL}_n(\mathbb F_p)|=\frac{|\operatorname{SL}_n(\mathbb F_p)|}{\gcd(n,p-1)}.
$$

</v-click>

---

# Simplicity of $\operatorname{PSL}_n(\mathbb F_p)$

**Theorem (Jordan, Dickson).** $\operatorname{PSL}_n(\mathbb F_p)$ is simple
**except** in two small cases:

<v-click>

$$
\operatorname{PSL}_2(\mathbb F_2)\cong S_3,\qquad
\operatorname{PSL}_2(\mathbb F_3)\cong A_4.
$$

Both are solvable, hence not simple.

</v-click>

<v-click>

For all other $(n,p)$: $\operatorname{PSL}_n(\mathbb F_p)$ is simple.

</v-click>

<v-click>

Foreshadowing: $G_2(\mathbb F_2)$ is also non-simple — same small-characteristic
flavour.

</v-click>

---

# Camille Jordan (1838–1922)

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 0.92rem;">

French mathematician. His *Traité des substitutions et des équations
algébriques* (1870) was the first systematic textbook on group theory after
Galois — and the first complete treatment of permutation groups,
$k$-transitivity, and what we now call simple and solvable groups.

<v-click>

In the same volume Jordan proved the simplicity of
$\operatorname{PSL}_2(\mathbb F_p)$ for $p\ge 5$, the case $n=2$ of the
theorem we just quoted.

</v-click>

<v-click>

His name is also attached to the Jordan curve theorem, Jordan canonical form,
and (jointly with Hölder) the Jordan–Hölder theorem we used in L08.

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/camille-jordan.jpg" style="height: 220px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">C. Jordan (1838–1922)</div>

</div>
</div>

---

# Leonard Eugene Dickson (1874–1954)

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 0.92rem;">

American algebraist; first PhD in mathematics at the University of Chicago
(1896). His book *Linear Groups, with an Exposition of the Galois Field
Theory* (1901) was the first systematic treatment of the finite linear
groups $\operatorname{GL}_n(\mathbb F_q)$, $\operatorname{PSL}_n(\mathbb F_q)$
and their simplicity.

<v-click>

Dickson completed the simplicity theorem for $\operatorname{PSL}_n(\mathbb F_q)$
in arbitrary $n$ and $q$, extending Jordan's $n=2$ case.

</v-click>

<v-click>

In 1905 he constructed the finite groups of type $G_2$ and proved their
simplicity — we will return to this when we discuss $G_2(\mathbb F_p)$ in
Part IV.

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/leonard-dickson.jpg" style="height: 220px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">L. E. Dickson (1874–1954)</div>

</div>
</div>

---

# Beautiful Coincidences

<div style="font-size: 0.92rem;">

| Group | Order | Isomorphism |
|---|---|---|
| $\operatorname{PSL}_2(\mathbb F_5)$ | $60$ | $A_5$ |
| $\operatorname{PSL}_2(\mathbb F_7)$ | $168$ | $\operatorname{GL}_3(\mathbb F_2)$ |
| $\operatorname{PSL}_2(\mathbb F_9)$ | $360$ | $A_6$ |
| $\operatorname{PSL}_4(\mathbb F_2)$ | $20\,160$ | $A_8$ |

</div>

<v-click>

These are the only "exceptional isomorphisms" between alternating and
$\operatorname{PSL}$ groups.

</v-click>

<v-click>

After them, the two families part ways forever.

</v-click>

---

# Summary of Example 1

$\operatorname{PSL}_n(\mathbb F_p)$ gives an **infinite family** of finite
simple groups, parametrised by $(n,p)$.

<v-click>

Together with $A_n$, this is the second infinite family we know.

</v-click>

<v-click>

What the family looks like:

- a uniform construction (linear algebra over $\mathbb F_p$),
- a clean order formula,
- a few small-$(n,p)$ exceptions where simplicity fails.

</v-click>

<v-click>

This is the texture of **Lie-type** simple groups in general. Now we move to
two examples that look completely different.

</v-click>

---
layout: center
---

# Part III

## Example 2 — Mathieu's $M_{12}$ (sporadic)

---

# Sporadic Simple Groups

Two waves of discovery, separated by a century:

<v-click>

- **1861**, Émile Mathieu: the five Mathieu groups $M_{11},M_{12},M_{22},M_{23},M_{24}$.

</v-click>

<v-click>

- **1965–1982**: $21$ further sporadic groups discovered, ending with the
  **Monster** of order $\approx 8\times 10^{53}$.

</v-click>

<v-click>

Total: $26$ finite simple groups belonging to **none** of the four infinite
families.

</v-click>

<v-click>

We focus on the smallest one with a clean construction: $M_{12}$.

</v-click>

---

# Steiner Systems

To find a sporadic simple group, the strategy is: build a **rigid
combinatorial structure**, then take its automorphism group.

<v-click>

**Definition (Steiner, 1853).** A **Steiner system** $S(t,k,v)$ consists of:

- a finite set $X$ with $|X|=v$ (the **points**);
- a collection $\mathcal B$ of $k$-subsets of $X$ (the **blocks**),

subject to one axiom:

$$
\boxed{\text{every }t\text{-subset of }X\text{ is contained in \emph{exactly one} block.}}
$$

</v-click>

<v-click>

The condition "exactly one" is what makes the system rigid: the small parts
($t$-subsets) completely determine the larger parts ($k$-subsets) once the
block collection is fixed.

</v-click>

---

# How Many Blocks?

A Steiner system $S(t,k,v)$ has

$$
|\mathcal B|=\frac{\binom{v}{t}}{\binom{k}{t}}
$$

blocks.

<v-click>

**Why.** Count pairs $(T,B)$ where $T$ is a $t$-subset of $X$ and $B$ is a
block containing $T$.

- Counting by $T$: each $t$-subset is in exactly one block, so the count is
  $\binom{v}{t}$.
- Counting by $B$: each $k$-block contains $\binom{k}{t}$ different
  $t$-subsets, so the count is $|\mathcal B|\cdot\binom{k}{t}$.

</v-click>

<v-click>

Equating gives the formula. So $\binom{k}{t}$ must divide $\binom{v}{t}$ for
the system to exist — already a strong restriction on $(t,k,v)$.

</v-click>

---

# Example 1: $S(2,3,7)$ — the Fano Plane

<div style="display: flex; gap: 1.5rem; align-items: flex-start;">
<div style="flex: 1; font-size: 0.94rem;">

- **Points.** $X=\{1,2,3,4,5,6,7\}$.

- **Blocks** (the "lines"):

$$
\begin{aligned}
&\{1,2,3\},\ \{1,4,5\},\ \{1,6,7\},\\
&\{2,4,6\},\ \{2,5,7\},\\
&\{3,4,7\},\ \{3,5,6\}.
\end{aligned}
$$

<v-click>

- **Block count check.** $\binom{7}{2}/\binom{3}{2}=21/3=7$. ✓

</v-click>

<v-click>

- Every pair of points lies in **exactly one** line. This is the smallest
  projective plane.

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/fano-plane.svg" style="height: 230px;" />

<div style="font-size: 0.7rem; opacity: 0.6; margin-top: 0.4rem;">$S(2,3,7)$ — the Fano plane</div>

</div>
</div>

---

# Fano Plane: Algebraic Interpretation

The Fano plane has a clean linear-algebra description over $\mathbb F_2$:

<v-click>

- **Points** $\;\longleftrightarrow\;$ nonzero vectors of $\mathbb F_2^3$
  (there are $2^3-1=7$ of them);
- **Lines** $\;\longleftrightarrow\;$ $2$-dimensional subspaces of $\mathbb F_2^3$,
  each containing $3$ nonzero vectors.

So the Fano plane is the projective plane $\mathbb P^2(\mathbb F_2)$.

</v-click>

<v-click>

**Group-theoretic version.** Identifying $\mathbb F_2^3$ with the additive
group $(\mathbb Z/2)^3$:

- the $7$ points are the non-identity elements of $(\mathbb Z/2)^3$;
- the $7$ lines are its $7$ subgroups of order $4$, each $\cong(\mathbb Z/2)^2$.

</v-click>

<v-click>

**Automorphism group.**

$$
\operatorname{Aut}(\text{Fano plane})=\operatorname{GL}_3(\mathbb F_2)\cong\operatorname{PSL}_2(\mathbb F_7),
\qquad |\cdot|=168,
$$

the second smallest non-abelian simple group.

</v-click>

---

# Example 2: $S(3,4,8)$

The next-simplest Steiner system, one parameter step up.

<v-click>

- **Points.** $X=\{1,2,\ldots,8\}$.

- **Block count.** $\binom{8}{3}/\binom{4}{3}=56/4=14$ blocks of size $4$.

</v-click>

<v-click>

- Every $3$-subset of $X$ lies in exactly one block.

</v-click>

<v-click>

- $\operatorname{Aut}\bigl(S(3,4,8)\bigr)\cong\operatorname{AGL}_3(\mathbb F_2)$,
  of order $1344$, acting **$3$-transitively** on the $8$ points.

</v-click>

<v-click>

**Existence is rare.** For most parameters $(t,k,v)$ no Steiner system exists
at all. The ones that do are highly constrained — that constraint is exactly
what forces a large, transitive automorphism group.

</v-click>

---

# Why Steiner Systems → Transitive Groups

Let $G=\operatorname{Aut}(S(t,k,v))$, the permutations of $X$ preserving the
block collection $\mathcal B$.

<v-click>

**Heuristic.** Any two $t$-subsets "look alike" inside $S(t,k,v)$:
each lies in a unique block, with the rest of $X$ playing the same role around
it.

</v-click>

<v-click>

So one expects $G$ to send any $t$-subset to any other — i.e. to act
**$t$-transitively** on $X$.

</v-click>

<v-click>

For the parameter set $(t,k,v)=(5,6,12)$ this turns out to be true, and the
resulting group $G$ is also **simple**. That group is $M_{12}$.

</v-click>

---

# The Steiner System $S(5,6,12)$

**Fact (Witt, 1938).** Up to isomorphism there is a **unique** Steiner system
$S(5,6,12)$.

<v-click>

- Underlying set: $X=\{1,2,\ldots,12\}$.
- Blocks ("hexads"): a specific collection of $6$-subsets.
- Number of blocks (from the formula on the previous slide):

$$
|\mathcal B|=\frac{\binom{12}{5}}{\binom{6}{5}}=\frac{792}{6}=132.
$$

</v-click>

<v-click>

This $S(5,6,12)$ is the unique Steiner system of "Mathieu type". The next one
up the ladder is $S(5,8,24)$ — the basis of $M_{24}$ — and there are no
others with $t\ge 4$.

</v-click>

---

# Constructing the Blocks: Setup

We build the $132$ hexads as a single orbit of a group from Part II.

<v-click>

**Step 1.** Identify the $12$ points with the projective line

$$
X\;\cong\;\mathbb P^1(\mathbb F_{11})=\mathbb F_{11}\cup\{\infty\}=\{0,1,\ldots,10,\infty\}.
$$

</v-click>

<v-click>

**Step 2.** Let $\operatorname{PSL}_2(\mathbb F_{11})$ act on $X$ by Möbius
maps $z\mapsto (az+b)/(cz+d)$, $ad-bc=1$. Order $660$, acting $2$-transitively
on the $12$ points.

</v-click>

<v-click>

**Step 3.** Choose the $6$-subset

$$
B_0=\{\infty\}\cup\{\text{nonzero squares mod }11\}=\{\infty,1,3,4,5,9\}.
$$

</v-click>

---

# Constructing the Blocks: The Orbit

**Step 4.** Form the $\operatorname{PSL}_2(\mathbb F_{11})$-orbit of $B_0$:

$$
\mathcal B:=\bigl\{\,g\cdot B_0:\ g\in\operatorname{PSL}_2(\mathbb F_{11})\,\bigr\}.
$$

<v-click>

A direct check (Witt, 1938) shows $|\operatorname{Stab}(B_0)|=5$, so the orbit
has size

$$
|\mathcal B|=\frac{|\operatorname{PSL}_2(\mathbb F_{11})|}{|\operatorname{Stab}(B_0)|}=\frac{660}{5}=132,
$$

precisely the predicted number of hexads.

</v-click>

<v-click>

These $132$ hexads are exactly the blocks of $S(5,6,12)$.

</v-click>

---

# Two Layers of Symmetry

The construction shows two nested groups of permutations:

<div style="font-size: 0.94rem;">

| Group | Order | Action |
|---|---|---|
| $\operatorname{PSL}_2(\mathbb F_{11})$ | $660$ | $2$-transitive on $\mathbb P^1(\mathbb F_{11})$ |
| $M_{12}:=\operatorname{Aut}(S(5,6,12))$ | $95\,040$ | sharply $5$-transitive on $\{1,\ldots,12\}$ |

</div>

<v-click>

$\operatorname{PSL}_2(\mathbb F_{11})\subset M_{12}$ is a proper inclusion: the
quotient of orders is $95\,040/660=144$.

</v-click>

<v-click>

So $M_{12}$ adds permutations beyond Möbius which still preserve
the block set $\mathcal B$. Those extra permutations are exactly what makes
$M_{12}$ jump from $3$-transitive to $5$-transitive.

</v-click>

<v-click>

To make "$k$-transitive" precise, we need a single definition.

</v-click>

---

# $k$-Transitivity

Let $G$ act on a set $X$ with $|X|=n$.

**Definition.** $G$ acts **$k$-transitively** on $X$ if for any two ordered
$k$-tuples of distinct points

$$
(x_1,\ldots,x_k)\quad\text{and}\quad (y_1,\ldots,y_k)
$$

there exists $g\in G$ such that $g(x_i)=y_i$ for all $i=1,\ldots,k$.

<v-click>

In words: $G$ "can carry any $k$-tuple to any other $k$-tuple".

</v-click>

<v-click>

- **$1$-transitive** = transitive (one orbit).
- **$2$-transitive** ⟹ transitive on **pairs** of distinct points.
- **$k$-transitive** ⟹ $(k-1)$-transitive (forget the last coordinate).

</v-click>

---

# How Restrictive Is $k$-Transitivity?

If $G$ is $k$-transitive on $n$ points, the orbit of any $k$-tuple of distinct
points has size $n(n-1)\cdots(n-k+1)$. By orbit–stabilizer:

$$
|G|\ \ge\ n(n-1)(n-2)\cdots(n-k+1).
$$

<v-click>

**Examples.**

- $S_n$ is $n$-transitive: $|S_n|=n!$.
- $A_n$ is $(n-2)$-transitive (any 3-cycle moves any pair into any pair, etc.).

</v-click>

<v-click>

**Theorem (Jordan, completed using CFSG).** For $n\ge 6$, the only
$5$-transitive groups on $n$ points are

$$
\boxed{S_n,\quad A_{n+2},\quad M_{12}\ (n=12),\quad M_{24}\ (n=24).}
$$

</v-click>

<v-click>

Outside the obvious $S_n,A_{n+2}$ tower, **only two** $5$-transitive groups
exist in all of finite group theory.

</v-click>

---

# Back to $M_{12}$: Order

**Fact.** $M_{12}$ acts $5$-transitively on $\{1,\ldots,12\}$, and the
stabilizer of any 5-tuple of distinct points is trivial.

<v-click>

Therefore the orbit of one $5$-tuple has size $|M_{12}|$, and equals the total
number of ordered $5$-tuples of distinct points:

$$
|M_{12}|=12\cdot 11\cdot 10\cdot 9\cdot 8=95\,040.
$$

</v-click>

<v-click>

So $M_{12}$ achieves the lower bound from the previous slide **with equality**.
That is the strongest form of $5$-transitivity possible: $M_{12}$ is
**sharply $5$-transitive**.

</v-click>

---

# $M_{11}$ Lives Inside

The pointwise stabilizer of one point is

$$
M_{11}:=\operatorname{Stab}_{M_{12}}(12)\le M_{12}.
$$

<v-click>

By orbit–stabilizer:

$$
|M_{11}|=\frac{|M_{12}|}{12}=\frac{95\,040}{12}=7920.
$$

</v-click>

<v-click>

$M_{11}$ acts $4$-transitively on $\{1,\ldots,11\}$.

</v-click>

<v-click>

The same theorem (now $4$-transitive case) gives an even shorter list:
$S_n$, $A_{n+2}$, $M_{11}$, $M_{12}$, $M_{23}$, $M_{24}$.

</v-click>

---

# What Else $M_{12}$ Touches

- $M_{12}$ contains two non-conjugate copies of $S_6$, swapped by an outer
  automorphism — this is **the** unique exceptional outer automorphism
  $\operatorname{Out}(S_6)=\mathbb Z/2$.

<v-click>

- $M_{12}$ is closely tied to the **binary Golay code** and leads, by
  doubling, to $M_{24}$, the Leech lattice, and (much further upstream) the
  Monster.

</v-click>

---

# Another Face: the Ternary Golay Code

So far $M_{12}=\operatorname{Aut}(S(5,6,12))$ — a permutation group on $12$
points. The same group has a second concrete realisation, of "linear" type.

<v-click>

**Ternary Golay code.** There is a $6$-dimensional subspace

$$
\mathcal G\;\subset\;\mathbb F_3^{12}
$$

(unique up to equivalence) in which every nonzero vector has at least $6$
nonzero coordinates, and which is self-dual under the standard inner product
on $\mathbb F_3^{12}$. This is the **extended ternary Golay code**.

</v-click>

<v-click>

The combinatorial rigidity of $\mathcal G$ is, again, the source of a large
symmetry group.

</v-click>

---

# $M_{12}\subset\operatorname{PGL}_6(\mathbb F_3)$

**Theorem.** The group of permutations of the $12$ coordinates of
$\mathbb F_3^{12}$ that send $\mathcal G$ to itself, together with sign
changes preserving $\mathcal G$, is a central double cover

$$
2.M_{12}\;\twoheadrightarrow\;M_{12},
$$

with kernel $\langle-I\rangle$ inside $\operatorname{GL}(\mathcal G)$.

<v-click>

Restricting the action to $\mathcal G\cong\mathbb F_3^6$ and modding out the
central $\pm I$:

$$
\boxed{\,M_{12}\;\subset\;\operatorname{PGL}_6(\mathbb F_3).\,}
$$

</v-click>

<v-click>

Two faces of the same group: a $5$-transitive permutation group on $12$
points (combinatorial), and a small linear subgroup of
$\operatorname{PGL}_6(\mathbb F_3)$ (algebraic).

</v-click>

---

# Summary of Example 2

$M_{12}$ is **sporadic**: not a member of any infinite family.

<v-click>

It exists because $S(5,6,12)$ exists.

</v-click>

<v-click>

After Mathieu's five sporadics in 1861, none were found for over a century —
then between 1965 and 1982 the remaining $21$ sporadics emerged, ending with
the Monster.

</v-click>

---
layout: center
---

# Part IV

## Example 3 — $G_2$ (exceptional Lie type), via the Octonions

---

# Hurwitz's Theorem

**Theorem (Hurwitz, 1898).** Up to isomorphism, the only finite-dimensional
normed division algebras over $\mathbb R$ are

<div style="font-size: 0.96rem;">

| Algebra | $\dim_{\mathbb R}$ | Properties |
|---|:---:|---|
| $\mathbb R$ | $1$ | the reals |
| $\mathbb C$ | $2$ | commutative, associative |
| $\mathbb H$ | $4$ | associative, **not** commutative |
| $\mathbb O$ | $8$ | alternative, **not** associative |

</div>

<v-click>

Each is built from the previous by **Cayley–Dickson doubling**, and at each
step one property is lost.

</v-click>

---

# Adolf Hurwitz (1859–1919)

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 0.92rem;">

German mathematician, student of Felix Klein, professor at ETH Zürich
(1892–1919). He was a master of complex analysis, number theory, and the
algebra of forms.

<v-click>

His **1898** paper *Über die Composition der quadratischen Formen von
beliebig vielen Variabeln* showed that the multiplicative norm identity
$N(xy)=N(x)N(y)$ admits real solutions only in dimensions $1,2,4,8$ — the
classification result behind the table above.

</v-click>

<v-click>

His name is also attached to the **Hurwitz zeta function**, the **Hurwitz
quaternions**, and the **Hurwitz automorphisms theorem** (a Riemann surface
of genus $g\ge 2$ has at most $84(g-1)$ automorphisms).

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/hurwitz.jpg" style="height: 220px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">A. Hurwitz (1859–1919)</div>

</div>
</div>

---

# Cayley–Dickson Doubling

Given an algebra $A$ with conjugation $a\mapsto\bar a$, define $A\oplus A$ with

$$
(a,b)(c,d):=(ac-\bar d b,\ d a+b\bar c),
$$

$$
\overline{(a,b)}:=(\bar a,-b).
$$

<v-click>

- $\mathbb C=$ doubling of $\mathbb R$.

</v-click>

<v-click>

- $\mathbb H=$ doubling of $\mathbb C$ — loses commutativity.

</v-click>

<v-click>

- $\mathbb O=$ doubling of $\mathbb H$ — loses associativity (keeps
  alternativity: $(xx)y=x(xy)$).

</v-click>

<v-click>

- Doubling once more produces the sedenions, which are **not** a division
  algebra. The tower stops.

</v-click>

---

# Arthur Cayley (1821–1895)

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 0.92rem;">

British mathematician, founding figure of group theory and matrix algebra.

<v-click>

He gave the first abstract definition of a group; **Cayley's theorem** states
that every group embeds in some symmetric group.

</v-click>

<v-click>

In **1845** he wrote down what we now call the **octonions**, doubling
Hamilton's quaternions $\mathbb H$ to an 8-dimensional algebra. (J. T. Graves
discovered them independently a few months earlier; the systematic *doubling*
recipe was generalized by L. E. Dickson, hence "Cayley–Dickson".)

</v-click>

<v-click>

Author of more than $900$ papers; his name lives on in the Cayley table,
Cayley graph, Cayley–Hamilton theorem, and the Cayley transform.

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/cayley.jpg" style="height: 220px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">A. Cayley (1821–1895)</div>

</div>
</div>

---

# What an Octonion Looks Like

$\mathbb O$ has basis $1,e_1,\ldots,e_7$ over $\mathbb R$, with

$$
e_i^2=-1,\qquad e_ie_j=-e_je_i\quad(i\neq j).
$$

<v-click>

The full multiplication table is encoded by the **Fano plane** — $7$ lines,
each carrying a copy of imaginary quaternions.

</v-click>

<v-click>

Norm $N(x):=x\bar x\in\mathbb R$ is multiplicative:

$$
N(xy)=N(x)\,N(y)
$$

— the **eight-square identity**.

</v-click>

---

# Tower of Automorphism Groups

<div style="font-size: 0.92rem;">

| Algebra | $\operatorname{Aut}(\cdot)$ | $\dim$ |
|---|---|:---:|
| $\mathbb R$ | trivial | $0$ |
| $\mathbb C$ | $\mathbb Z/2$ (complex conjugation) | $0$ |
| $\mathbb H$ | $\operatorname{SO}(3)$ (rotations of $\operatorname{Im}\mathbb H$) | $3$ |
| $\mathbb O$ | $\boxed{G_2}$ | $14$ |

</div>

<v-click>

Each step up the algebra tower, the automorphism group jumps in dimension.

</v-click>

<v-click>

$$
\boxed{G_2:=\operatorname{Aut}(\mathbb O).}
$$

</v-click>

---

# Why $G_2$ Is "Exceptional"

**Theorem (Cartan, 1894).** Simple Lie algebras over $\mathbb C$ split into

- four classical infinite families: $A_n,B_n,C_n,D_n$;

<v-click>

- five **exceptional** Lie algebras: $G_2,F_4,E_6,E_7,E_8$.

</v-click>

<v-click>

$G_2$ is the smallest exceptional one. "Exceptional" means: not in any
infinite family, in the same spirit as $M_{11},\ldots,M_{24}$ are sporadic.

</v-click>

<v-click>

And $G_2=\operatorname{Aut}(\mathbb O)$ gives a beautifully concrete model.

</v-click>

---

# Élie Cartan (1869–1951)

<div style="display: flex; gap: 1.5rem;">
<div style="flex: 1; font-size: 0.92rem;">

French mathematician; one of the founders of modern differential geometry
and the theory of Lie groups.

<v-click>

His **1894 thesis** *Sur la structure des groupes de transformations finis et
continus* completed the classification of complex simple Lie algebras: four
classical infinite families $A_n, B_n, C_n, D_n$ and **five** exceptional
ones $G_2, F_4, E_6, E_7, E_8$.

</v-click>

<v-click>

Cartan also pioneered the theory of **spinors**, **exterior differential
forms** and **moving frames** in differential geometry. His son Henri Cartan
became one of the founders of Bourbaki and a leading algebraic topologist.

</v-click>

</div>
<div style="flex: 0 0 auto; display: flex; flex-direction: column; align-items: center;">

<img src="/elie-cartan.png" style="height: 220px; border-radius: 4px;" />

<div style="font-size: 0.7rem; opacity: 0.6;">É. Cartan (1869–1951)</div>

</div>
</div>

---

# $G_2$ over $\mathbb F_p$

The same definition works over any field.

<v-click>

For $p$ prime, define $\mathbb O_{\mathbb F_p}$ — the (split) octonion algebra
over $\mathbb F_p$ — by Cayley–Dickson doubling, replacing $\mathbb R$ with
$\mathbb F_p$.

</v-click>

<v-click>

$$
G_2(\mathbb F_p):=\operatorname{Aut}\bigl(\mathbb O_{\mathbb F_p}\bigr).
$$

</v-click>

<v-click>

$$
\boxed{|G_2(\mathbb F_p)|=p^6\,(p^6-1)(p^2-1).}
$$

</v-click>

<v-click>

(For prime-power $q=p^k$, replace $p$ by $q$. Building $\mathbb F_q$ needs Galois
theory, so today we keep $p$ prime.)

</v-click>

---

# Simplicity over $\mathbb F_p$

**Theorem (Dickson, 1905).** $G_2(\mathbb F_p)$ is simple for every prime
$p\ge 3$.

<v-click>

**Exception.** $G_2(\mathbb F_2)$ has order $12\,096=2\cdot 6048$ and is **not**
simple.

</v-click>

<v-click>

Its derived subgroup is

$$
G_2(\mathbb F_2)'\cong\operatorname{PSU}_3(\mathbb F_3),
$$

a classical Lie type group of order $6048$.

</v-click>

<v-click>

Same flavour as $\operatorname{PSL}_2(\mathbb F_2)\cong S_3$ and
$\operatorname{PSL}_2(\mathbb F_3)\cong A_4$ — small characteristic spoils
simplicity.

</v-click>

---

# Smallest Examples

<div style="font-size: 0.92rem;">

| $p$ | $|G_2(\mathbb F_p)|$ | simple? |
|:---:|---|:---:|
| $2$ | $12\,096$ | no (derived $\cong\operatorname{PSU}_3(\mathbb F_3)$, order $6048$) |
| $3$ | $4\,245\,696$ | **yes** — smallest simple $G_2$ |
| $5$ | $5\,859\,000\,000$ | yes |
| $7$ | $\approx 6.64\times 10^{11}$ | yes |
| $11$ | $\approx 3.77\times 10^{14}$ | yes |

</div>

<v-click>

For each prime $p\ge 3$: a brand-new finite simple group of **exceptional Lie
type**.

</v-click>

---

# Summary of Example 3

$G_2$ wears two faces, both captured by one definition:

$$
\boxed{G_2=\operatorname{Aut}(\mathbb O).}
$$

<v-click>

- Over $\mathbb R$: a $14$-dim simple Lie group, exceptional.

</v-click>

<v-click>

- Over $\mathbb F_p$ (prime $p\ge 3$): a finite simple group, of exceptional
  Lie type — parallel to but distinct from $\operatorname{PSL}_n(\mathbb F_p)$.

</v-click>

---
layout: center
---

# Part V

## Looking Back

---

# CFSG as a Tree

```text
Finite simple groups
  |
  +-- cyclic Z_p
  |
  +-- alternating A_n   (n >= 5)
  |
  +-- Lie type
  |     +-- classical:    PSL, PSU, PSp, P-Omega over finite fields
  |     +-- exceptional:  G_2, F_4, E_6, E_7, E_8 + twisted
  |
  +-- 26 sporadic
        +-- Mathieu:  M_11, M_12, M_22, M_23, M_24
        +-- 20 more (1965-1982)
        +-- Monster   (~ 8 x 10^53)
```

<v-click>

Today's three examples sit on three different branches:
$\operatorname{PSL}_n(\mathbb F_p)$ on classical Lie, $G_2(\mathbb F_p)$ on
exceptional Lie, $M_{12}$ on sporadic. Together with $\mathbb Z_p$ (L01) and
$A_n$ (L04), we have now met an example from every branch.

</v-click>

---

# What the Three Examples Reveal

The classification has very different textures inside each family.

<v-click>

- **Classical Lie ($\operatorname{PSL}_n$).** A clean infinite family with a
  uniform construction (linear algebra) and a single small-characteristic
  defect.

</v-click>

<v-click>

- **Sporadic ($M_{12}$).** A handful of isolated groups built from rare
  combinatorial objects — there is no infinite family, and no construction
  that "explains them all".

</v-click>

<v-click>

- **Exceptional Lie ($G_2$).** Still an infinite family in $p$, but built from
  a non-associative algebra rather than from $\mathbb F_p^n$. A different
  algebraic phenomenon than $\operatorname{PSL}$.

</v-click>

<v-click>

CFSG is the statement that **these three textures, plus $\mathbb Z_p$ and
$A_n$, exhaust everything.**

</v-click>

---

# Bridges to Coming Chapters

**Bridge 1 — division rings.** Octonions are the last normed division
algebra. Ring theory begins with division rings.

<v-click>

**Bridge 2 — Galois of finite fields.** $G_2(\mathbb F_q)$ for $q=p^k$ uses
$\mathbb F_q$, whose construction is one of the first applications of Galois
theory. Its Galois group is cyclic, generated by the Frobenius.

</v-click>

---

# References — CFSG and Sporadic Groups

<div style="font-size: 0.84rem;">

- **Aschbacher, M.** *Finite Group Theory*. Cambridge Univ. Press, 2nd ed., 2000. — Standard reference for the structural side of CFSG.

- **Conway, J. H.; Sloane, N. J. A.** *Sphere Packings, Lattices and Groups*. Springer, 3rd ed., 1999. Ch. 10–11. — The Mathieu groups, $S(5,6,12)$, $S(5,8,24)$, the Golay code, the Leech lattice.

- **Wilson, R. A.** *The Finite Simple Groups*. Graduate Texts in Math. 251, Springer, 2009. — Modern textbook covering all four families with explicit constructions.

- **Solomon, R.** "A brief history of the classification of the finite simple groups." *Bull. Amer. Math. Soc.* 38 (2001), 315–352. — Historical overview of the CFSG project.

- **ATLAS of Finite Groups** (Conway, Curtis, Norton, Parker, Wilson, 1985). — Character tables, presentations, maximal subgroups for sporadic and small groups.

</div>

---

# References — Exceptional Groups

<div style="font-size: 0.84rem;">

- **Hurwitz, A.** "Über die Composition der quadratischen Formen von beliebig vielen Variabeln." *Nachr. Ges. Wiss. Göttingen* (1898), 309–316. — Classification of normed division algebras.

- **Cartan, É.** "Sur la structure des groupes de transformations finis et continus." Thèse, Paris, 1894. — Classification of complex simple Lie algebras, including $G_2,F_4,E_6,E_7,E_8$.

- **Dickson, L. E.** "A new system of simple groups." *Math. Ann.* 60 (1905), 137–150. — Construction and simplicity of $G_2(\mathbb F_q)$.

- **Springer, T. A.; Veldkamp, F. D.** *Octonions, Jordan Algebras and Exceptional Groups*. Springer Monographs, 2000. — $\mathbb O$, $G_2$, $F_4$, and the rest of the exceptional family.

- **Baez, J. C.** "The octonions." *Bull. Amer. Math. Soc.* 39 (2002), 145–205. — Highly readable survey: $\mathbb R,\mathbb C,\mathbb H,\mathbb O$ and the exceptional Lie algebras.

</div>

---

# What to Remember

<div style="font-size: 0.92rem;">

1. CFSG: every finite simple group is cyclic of prime order, alternating
   ($n\ge 5$), Lie type (classical or exceptional), or one of $26$ sporadic.

2. $\operatorname{PSL}_n(\mathbb F_p)$ — classical Lie, infinite family, simple
   except for $(n,p)=(2,2),(2,3)$.

3. $M_{12}=\operatorname{Aut}(S(5,6,12))$ — sporadic, $5$-transitive on $12$
   points, of order $95\,040$. Blocks built as one $\operatorname{PSL}_2(\mathbb F_{11})$-orbit.

4. $G_2:=\operatorname{Aut}(\mathbb O)$, with finite version $G_2(\mathbb F_p)$
   of order $p^6(p^6-1)(p^2-1)$ — exceptional Lie, simple for $p\ge 3$.

</div>

---

# Homework (Lecture 9)

**Problem 1. Mathieu and stabilizers.**

Let $G$ act $k$-transitively on $n$ points ($k\ge 1,\ n\ge k$).

a. Show that the stabilizer of any one point is $(k-1)$-transitive on the
remaining $n-1$ points.

b. Use $5$-transitivity of $M_{12}$ on $\{1,\ldots,12\}$ to conclude
$|M_{11}|=7920$.

---

# Homework (Lecture 9)

**Problem 2. Octonion automorphisms.**

Let $\varphi:\mathbb O\to\mathbb O$ be an $\mathbb R$-algebra automorphism.

a. Show that $\varphi(1)=1$.

b. Show that $\varphi$ commutes with conjugation: $\varphi(\bar x)=\overline{\varphi(x)}$.

c. Show that $\varphi$ preserves the norm $N(x)=x\bar x$.

d. Conclude that $\varphi$ restricts to an element of $\operatorname{O}(7)$ on
$\operatorname{Im}\mathbb O$, so $G_2\subseteq\operatorname{O}(7)$.

---

# Homework (Lecture 9)

**Problem 3. $G_2$ over $\mathbb F_p$.**

a. From the formula $|G_2(\mathbb F_p)|=p^6(p^6-1)(p^2-1)$, compute

$$
|G_2(\mathbb F_3)|\quad\text{and}\quad |G_2(\mathbb F_5)|.
$$

b. Verify $|G_2(\mathbb F_2)|=12\,096$ and check that
$12\,096=2\cdot 6048$ with $6048=|\operatorname{PSU}_3(\mathbb F_3)|$.

---
layout: center
---

# Questions?
