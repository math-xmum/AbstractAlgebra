---
title: "MAT205: Abstract Algebra II - Subnormal Series, Solvable and Nilpotent Groups"
math: katex
---

# MAT205: Abstract Algebra II

## Subnormal Series, Solvable and Nilpotent Groups

<br/>

**Ma, Jia-Jun** - Xiamen University Malaysia

---

# Goal

We have used normal subgroups to make quotient groups.

<v-click>

Today we use quotient groups repeatedly:

$$
G=G_0 \triangleright G_1 \triangleright G_2 \triangleright \cdots \triangleright G_n=1.
$$

</v-click>

<v-click>

Question:

$$
\boxed{\text{What do the successive quotients }G_i/G_{i+1}\text{ tell us about }G?}
$$

</v-click>

<v-click>

Topics:

1. subnormal series;
2. composition series;
3. solvable groups;
4. nilpotent groups.

</v-click>

---

# Examples Used

<div style="font-size: 0.88rem;">

| Group | Fact used |
|---|---|
| $\mathbb Z_n$ | finite cyclic abelian group |
| $S_3$ | solvable, not nilpotent |
| $D_4$ | non-abelian nilpotent group of order $8$ |
| $A_5$ | non-abelian simple group |

</div>

---
layout: center
---

# Part I

## Extensions and Subnormal Series

---

# Normal Subgroup and Extension

If $N\triangleleft G$, then

$$
1\longrightarrow N\longrightarrow G\longrightarrow G/N\longrightarrow 1.
$$

<v-click>

This is a short exact sequence:

$$
\boxed{G\text{ is an extension of }G/N\text{ by }N.}
$$

</v-click>

<v-click>

The groups $N$ and $G/N$ do not determine $G$ up to isomorphism.

</v-click>

<v-click>

Example:

$$
1\to \mathbb Z_2\to \mathbb Z_4\to \mathbb Z_2\to 1,
\qquad
1\to \mathbb Z_2\to \mathbb Z_2\times\mathbb Z_2\to \mathbb Z_2\to 1.
$$

The two middle groups are not isomorphic.

</v-click>

---

# Example: $S_3$

The sign map gives

$$
1\longrightarrow A_3\longrightarrow S_3
\xrightarrow{\operatorname{sgn}}
\{\pm1\}\longrightarrow 1.
$$

<v-click>

The kernel and quotient are

$$
A_3\cong \mathbb Z_3,
\qquad
S_3/A_3\cong \mathbb Z_2.
$$

</v-click>

<v-click>

Therefore

$$
1\triangleleft A_3\triangleleft S_3
\quad\text{has abelian quotients.}
$$

</v-click>

---

# Subnormal Series

**Definition.** A **subnormal series** of $G$ is a chain

$$
G=G_0 \triangleright G_1 \triangleright \cdots \triangleright G_n=1
$$

such that

$$
G_{i+1}\triangleleft G_i
\qquad\text{for }0\le i<n.
$$

<v-click>

The factor groups are

$$
G_0/G_1,\quad G_1/G_2,\quad \ldots,\quad G_{n-1}/G_n.
$$

</v-click>

<v-click>

Normality is only required **one step at a time**.

</v-click>

---

# Normal Series

A **normal series** is a stronger kind of subnormal series:

$$
G=G_0 \triangleright G_1 \triangleright \cdots \triangleright G_n=1
$$

where each $G_i\triangleleft G$, not only $G_i\triangleleft G_{i-1}$.

<v-click>

So:

$$
\text{normal series} \Longrightarrow \text{subnormal series}.
$$

</v-click>

<v-click>

Composition series are defined using subnormal series because normality is not transitive.

</v-click>

---

# Normality Is Not Transitive

Let $D_4=\langle r,s\mid r^4=s^2=1,\ srs^{-1}=r^{-1}\rangle$, the symmetry group of a square.

<v-click>

Set

$$
K=\langle r^2,s\rangle=\{1,r^2,s,r^2s\},
\qquad
H=\langle s\rangle.
$$

</v-click>

<v-click>

Then

$$
H\triangleleft K,
\qquad
K\triangleleft D_4,
\qquad
H\not\triangleleft D_4.
$$

</v-click>

<v-click>

Thus

$$
D_4 \supset K \supset H
$$

is a valid one-step-at-a-time normal chain, even though $H$ is not normal in $D_4$.

This is why a subnormal series only asks for one-step normality.

</v-click>

---

# Refinement

A series can be made longer by inserting extra subgroups.

<v-click>

Example in $\mathbb Z_{12}$:

$$
0 < \langle 3\rangle < \mathbb Z_{12}
$$

has factors

$$
\mathbb Z_4,\qquad \mathbb Z_3.
$$

</v-click>

<v-click>

Since $\mathbb Z_4$ still has a nontrivial proper subgroup, refine the chain:

$$
0 < \langle 6\rangle < \langle 3\rangle < \mathbb Z_{12}.
$$

</v-click>

<v-click>

Now every factor is cyclic of prime order:

$$
\mathbb Z_2,\quad \mathbb Z_2,\quad \mathbb Z_3.
$$

</v-click>

---
layout: center
---

# Part II

## Composition Series

---

# Simple Groups

**Definition.** A nontrivial group $S$ is **simple** if its only normal subgroups are

$$
1\quad\text{and}\quad S.
$$

<v-click>

Examples:

$$
\mathbb Z_p\quad (p\text{ prime})
$$

is simple.

</v-click>

<v-click>

$A_5$ is simple and non-abelian.

</v-click>

<v-click>

For $n\ge 5$, $A_n$ is simple and non-abelian.

</v-click>

---

# Composition Series

**Definition.** A **composition series** is a subnormal series

$$
G=G_0 \triangleright G_1 \triangleright \cdots \triangleright G_n=1
$$

whose factors

$$
G_i/G_{i+1}
$$

are all simple.

<v-click>

The number $n$ is the **composition length**.

</v-click>

<v-click>

Every finite group has a composition series.

</v-click>

---

# Example: $S_3$

Use the chain

$$
1\triangleleft A_3\triangleleft S_3.
$$

<v-click>

The factors are

$$
A_3/1\cong \mathbb Z_3,
\qquad
S_3/A_3\cong \mathbb Z_2.
$$

</v-click>

<v-click>

Both are simple, so this is a composition series.

</v-click>

<v-click>

Composition factors:

$$
\mathbb Z_3,\quad \mathbb Z_2.
$$

</v-click>

---

# Example: $\mathbb Z_{12}$

One composition series is

$$
0 < \langle 6\rangle < \langle 3\rangle < \mathbb Z_{12}.
$$

<v-click>

The factor orders are

$$
2,\quad 2,\quad 3.
$$

</v-click>

<v-click>

Another series can put the prime factors in a different order.

</v-click>

<v-click>

Jordan-Holder says the unordered list is intrinsic:

$$
12=2\cdot 2\cdot 3.
$$

</v-click>

---

# Direct Product Calculation

<div style="font-size: 0.76rem; line-height: 1.16;">

Suppose

$$
G=G_0\ge G_1\ge\cdots\ge G_m=1,
\qquad
H=H_0\ge H_1\ge\cdots\ge H_n=1
$$

are composition series.

<v-click>

Then $G\times H$ has the composition series

$$
G_0\times H
\ge G_1\times H
\ge\cdots\ge
G_m\times H
=1\times H_0
\ge 1\times H_1
\ge\cdots\ge
1\times H_n.
$$

</v-click>

<v-click>

The factors are

$$
\frac{G_i\times H}{G_{i+1}\times H}\cong \frac{G_i}{G_{i+1}},
\qquad
\frac{1\times H_j}{1\times H_{j+1}}\cong \frac{H_j}{H_{j+1}}.
$$

</v-click>

<v-click>

So the composition factors of $G\times H$ are the composition factors of $G$
and $H$, with multiplicity.

</v-click>

</div>

---

# Example: $S_3\times \mathbb Z_{12}$

<div style="font-size: 0.78rem; line-height: 1.16;">

Use

$$
S_3\ge A_3\ge 1,
\qquad
\mathbb Z_{12}\ge \langle 3\rangle\ge \langle 6\rangle\ge 0.
$$

<v-click>

Then

$$
S_3\times \mathbb Z_{12}
\ge A_3\times \mathbb Z_{12}
\ge 1\times \mathbb Z_{12}
\ge 1\times \langle 3\rangle
\ge 1\times \langle 6\rangle
\ge 1.
$$

</v-click>

<v-click>

The factors are

$$
\mathbb Z_2,\quad
\mathbb Z_3,\quad
\mathbb Z_3,\quad
\mathbb Z_2,\quad
\mathbb Z_2.
$$

</v-click>

<v-click>

Thus the composition length is $5$.

</v-click>

</div>

---

# Jordan-Holder Theorem

<div class="grid grid-cols-[1.05fr_0.95fr] gap-8 items-center">

<div style="font-size: 0.9rem;">

**Theorem.** If a group $G$ has two composition series, then:

<v-clicks>

- the two series have the same length;
- after reordering, their simple factors are isomorphic.

</v-clicks>

<v-click>

So the composition factors are well-defined up to order.

</v-click>

</div>

<div>
  <img src="/jordan-holder-two-series.svg" style="height: 310px; margin: 0 auto;" />
</div>

</div>

---

# Camille Jordan and Otto Holder

<div class="grid grid-cols-2 gap-8 items-start">

<div style="text-align: center;">
  <img src="/camille-jordan.jpg" style="height: 285px; width: 225px; object-fit: cover; border: 1px solid #bbb; border-radius: 6px; margin: 0 auto;" />
  <div style="font-size: 0.9rem; margin-top: 0.45rem;"><strong>Camille Jordan</strong> (1838-1922)</div>
  <div style="font-size: 0.73rem; line-height: 1.2;">Developed early structure theory of finite groups and permutation groups.</div>
</div>

<div style="text-align: center;">
  <img src="/otto-holder.jpg" style="height: 285px; width: 225px; object-fit: cover; border: 1px solid #bbb; border-radius: 6px; margin: 0 auto;" />
  <div style="font-size: 0.9rem; margin-top: 0.45rem;"><strong>Otto Holder</strong> (1859-1937)</div>
  <div style="font-size: 0.73rem; line-height: 1.2;">Proved the modern uniqueness statement for composition factors.</div>
</div>

</div>

<div style="font-size: 0.58rem; margin-top: 0.4rem;">
Photos: Wikimedia Commons.
</div>

---

# Consequences of Jordan-Holder

Jordan-Holder is not saying the subgroup chain is unique.

<v-click>

It says the composition factors are unique up to isomorphism and order.

</v-click>

<v-click>

The composition length is also independent of the chosen composition series.

</v-click>

<v-click>

The invariant is

$$
\boxed{\{\,G_i/G_{i+1}\,\}\text{ as a multiset of isomorphism classes}.}
$$

</v-click>

---

# Composition Factors Do Not Determine $G$

<div style="font-size: 0.84rem;">

Composition factors do not determine the isomorphism type of $G$.

<v-click>

| Groups | Same composition factors |
|---|---|
| $\mathbb Z_4$ and $\mathbb Z_2\times\mathbb Z_2$ | $\mathbb Z_2,\mathbb Z_2$ |
| $\mathbb Z_6$ and $S_3$ | $\mathbb Z_3,\mathbb Z_2$ |

</v-click>

<v-click>

Both rows give non-isomorphic groups with the same composition factors.

</v-click>

<v-click>

The extension structure is not determined by the composition factors.

</v-click>

<v-click>

The next definition imposes a condition on the factor groups:

$$
\boxed{G_i/G_{i+1}\text{ abelian for all }i.}
$$

</v-click>

</div>

---
layout: center
---

# Part III

## Solvable Groups

---

# Solvable Groups

**Definition.**

$G$ is **solvable** if there is a subnormal series

$$
G=G_0\ge G_1\ge\cdots\ge G_n=1
$$

with $G_{i+1}\triangleleft G_i$ and

$$
G_i/G_{i+1}\text{ abelian for }0\le i<n.
$$

<v-click>

This is the definition used in the Galois theorem on solvability by radicals.

</v-click>

---

# Abelian Factors and Commutators

<div style="font-size: 0.8rem; line-height: 1.18;">

For a subnormal series

$$
G=G_0\ge G_1\ge\cdots\ge G_n=1,
$$

the factor $G_i/G_{i+1}$ is abelian iff

$$
G_i/G_{i+1}\text{ abelian}
\Longleftrightarrow
[G_i,G_i]\le G_{i+1}.
$$

<v-click>

Thus a subnormal series has abelian factors iff

$$
[G_i,G_i]\le G_{i+1}
\quad\text{for all }i.
$$

</v-click>

<v-click>

This is the local commutator condition for solvability.

</v-click>

</div>

---

# Derived Series

Define

$$
G^{(0)}=G,
\qquad
G^{(r+1)}=[G^{(r)},G^{(r)}].
$$

<v-click>

Then

$$
G^{(r)}/G^{(r+1)}
$$

is abelian for every $r$.

</v-click>

<v-click>

The series

$$
G=G^{(0)}\ge G^{(1)}\ge G^{(2)}\ge\cdots
$$

is the **derived series**.

</v-click>

---

# Derived-Series Criterion

**Theorem.**

$$
G\text{ is solvable}
\Longleftrightarrow
G^{(m)}=1\text{ for some }m.
$$

<v-click>

The least such $m$ is the **derived length** of $G$.

</v-click>

<v-click>

This criterion is equivalent to the existence of a subnormal series with abelian factors.

</v-click>

<v-click>

For finite groups, this criterion can be checked by computing commutator subgroups.

</v-click>

---

# Example: $S_3$

In $S_3$,

$$
[S_3,S_3]=A_3.
$$

<v-click>

Since $A_3$ is abelian,

$$
[A_3,A_3]=1.
$$

</v-click>

<v-click>

So

$$
S_3\triangleright A_3\triangleright 1
$$

is the derived series.

</v-click>

<v-click>

Therefore $S_3$ is solvable of derived length $2$.

</v-click>

---

# Example: $A_5$

$A_5$ is simple and non-abelian.

<v-click>

Its derived subgroup is normal:

$$
[A_5,A_5]\triangleleft A_5.
$$

</v-click>

<v-click>

Since $A_5$ is non-abelian, this subgroup is not $1$.

</v-click>

<v-click>

Since $A_5$ is simple, it must be all of $A_5$:

$$
[A_5,A_5]=A_5.
$$

</v-click>

<v-click>

So the derived series never shrinks. Hence $A_5$ is not solvable.

</v-click>

---

# Composition-Factor Test

**Theorem.** For finite groups:

$$
\boxed{
G\text{ is solvable}
\Longleftrightarrow
\text{all composition factors are cyclic of prime order}.
}
$$

<v-click>

Proof idea:

simple abelian groups are exactly

$$
\mathbb Z_p.
$$

</v-click>

<v-click>

A finite group is not solvable iff at least one composition factor is non-abelian simple.

</v-click>

---

# Solvable by Radicals

<div class="grid grid-cols-[1fr_0.7fr] gap-8 items-start">

<div style="font-size: 0.88rem;">

Let $f\in \mathbb Q[x]$, and let $L$ be its splitting field over $\mathbb Q$.

<v-click>

**Theorem (Galois).**
$f$ is solvable by radicals over $\mathbb Q$ iff

$$
\operatorname{Gal}(L/\mathbb Q)
$$

is a solvable group.

</v-click>

<v-click>

Here "solvable group" means the abelian-factor definition above.

</v-click>

</div>

<div style="text-align: center;">
  <img src="/galois.jpg" style="height: 315px; width: 240px; object-fit: cover; border: 1px solid #bbb; border-radius: 6px; margin: 0 auto;" />
  <div style="font-size: 0.7rem; margin-top: 0.35rem;">Evariste Galois. Wikimedia Commons.</div>
</div>

</div>

---

# Radical Extensions

Assume $K$ contains the $n$-th roots of unity.

<v-click>

Let

$$
L=K(\alpha),
\qquad
\alpha^n=a\in K,
$$

and assume $L/K$ is Galois.

</v-click>

<v-click>

For $\sigma\in \operatorname{Gal}(L/K)$,

$$
\sigma(\alpha)^n=a,
\qquad
\sigma(\alpha)=\zeta\alpha
\quad(\zeta\in\mu_n).
$$

</v-click>

<v-click>

Thus

$$
\operatorname{Gal}(L/K)\hookrightarrow \mu_n,
$$

so $\operatorname{Gal}(L/K)$ is abelian.

</v-click>

---

# Generic Polynomial

The polynomial

$$
x^n+t_1x^{n-1}+\cdots+t_n
\in \mathbb Q(t_1,\ldots,t_n)[x]
$$

has Galois group $S_n$ over $\mathbb Q(t_1,\ldots,t_n)$.

<v-click>

Also:

$$
S_n\text{ is solvable for }n\le 4,
\qquad
S_n\text{ is not solvable for }n\ge 5.
$$

</v-click>

<v-click>

Therefore the generic degree $n$ polynomial is solvable by radicals for $n\le 4$ and not solvable by radicals for $n\ge 5$.

</v-click>

---

# Burnside's Solvability Theorem

<div class="grid grid-cols-[0.72fr_1.15fr] gap-8 items-start">

<div style="text-align: center;">
  <img src="/william-burnside.jpeg" style="height: 300px; width: 235px; object-fit: cover; border: 1px solid #bbb; border-radius: 6px; margin: 0 auto;" />
  <div style="font-size: 0.72rem; margin-top: 0.35rem;">William Burnside. Wikimedia Commons.</div>
</div>

<div style="font-size: 0.9rem;">

**Theorem (Burnside).**
If

$$
|G|=p^a q^b
$$

for primes $p,q$, then $G$ is solvable.

<v-click>

By the composition-factor test, every composition factor of $G$ is cyclic of prime order.

</v-click>

<v-click>

In particular, no non-abelian simple group has order $p^aq^b$.

</v-click>

</div>

</div>

---
layout: center
---

# Part IV

## Nilpotent Tools and Examples

---

# Center

The center is

$$
Z(G)=\{z\in G: zg=gz\text{ for all }g\in G\}.
$$

<v-click>

It is a normal subgroup:

$$
Z(G)\triangleleft G.
$$

</v-click>

<v-click>

The center measures the elements that already commute with all of $G$:

$$
z\in Z(G)\Longleftrightarrow [z,g]=1\text{ for all }g\in G.
$$

</v-click>

---

# Upper Central Series

Define inductively:

$$
Z_0(G)=1.
$$

<v-click>

For $i\ge 0$, define $Z_{i+1}(G)$ by

$$
Z_{i+1}(G)/Z_i(G)
=
Z\bigl(G/Z_i(G)\bigr).
$$

</v-click>

<v-click>

This gives an ascending chain

$$
1=Z_0(G)\triangleleft Z_1(G)\triangleleft Z_2(G)\triangleleft \cdots.
$$

</v-click>

<v-click>

In particular, $Z_1(G)=Z(G)$.

</v-click>

---

# Lower Central Series

Define inductively:

$$
\gamma_1(G)=G,
\qquad
\gamma_{i+1}(G)=[\gamma_i(G),G].
$$

<v-click>

This gives

$$
G=\gamma_1(G)\triangleright \gamma_2(G)\triangleright \gamma_3(G)\triangleright\cdots.
$$

</v-click>

This is the **lower central series**.

---

# Central Series

A **central series** is a chain

$$
G=G_0\ge G_1\ge\cdots\ge G_c=1
$$

such that

$$
[G,G_i]\le G_{i+1}
\qquad (0\le i<c).
$$

<v-click>

Equivalently,

$$
G_i/G_{i+1}\le Z(G/G_{i+1}).
$$

</v-click>

---

# Nilpotent Groups

**Definition.**
$G$ is **nilpotent** if

$$
Z_c(G)=G
$$

for some $c\ge 0$.

<v-click>

Equivalently,

$$
\gamma_{c+1}(G)=1
$$

for some $c\ge 0$.

</v-click>

<v-click>

Equivalently, $G$ has a central series.

</v-click>

<v-click>

The least such $c$ is the **nilpotency class** of $G$.

</v-click>

---

# Abelian Groups

If $G$ is abelian, then

$$
Z(G)=G.
$$

<v-click>

So every nontrivial abelian group is nilpotent of class $1$.

</v-click>

<v-click>

Therefore:

$$
\boxed{\text{abelian}\Longrightarrow \text{nilpotent}.}
$$

</v-click>

---

# Example: $D_4$

<div style="font-size: 0.86rem;">

For the square group

$$
D_4=\langle r,s\mid r^4=s^2=1,\ srs^{-1}=r^{-1}\rangle,
$$

<v-click>

The center is $Z(D_4)=\{1,r^2\}$.

</v-click>

<v-click>

Since $D_4/Z(D_4)\cong \mathbb Z_2\times \mathbb Z_2$,

$$
[D_4,D_4]\le Z(D_4).
$$

</v-click>

<v-click>

Also $[D_4,Z(D_4)]=1$, so

$$
D_4>Z(D_4)>1
$$

is a central series.

</v-click>

<v-click>

$D_4$ is nilpotent of class $2$.

</v-click>

</div>

---

# Unitriangular Groups

<div style="font-size: 0.84rem;">

Let $U_n(\mathbb F_p)$ be the group of upper triangular matrices with $1$ on the diagonal.

<v-click>

Example:

$$
\begin{pmatrix}
1&*&*&*\\
0&1&*&*\\
0&0&1&*\\
0&0&0&1
\end{pmatrix}.
$$

</v-click>

<v-click>

Let $U_n^k$ be the subgroup whose first $k-1$ superdiagonals are zero.

</v-click>

<v-click>

One has

$$
[U_n^a,U_n^b]\le U_n^{a+b}.
$$

</v-click>

<v-click>

Thus

$$
U_n(\mathbb F_p)\text{ is nilpotent of class }n-1.
$$

</v-click>

</div>

---

# Finite $p$-Groups Are Nilpotent

We proved earlier:

$$
G\text{ a finite }p\text{-group}
\quad\Longrightarrow\quad
Z(G)\ne 1.
$$

<v-click>

Then apply the same fact to

$$
G/Z(G).
$$

</v-click>

<v-click>

Induction on $|G|$ gives $Z_c(G)=G$ for some $c$.

</v-click>

<v-click>

Therefore:

$$
\boxed{\text{Every finite }p\text{-group is nilpotent}.}
$$

</v-click>

---

# Finite Nilpotent Groups and Sylow Theory

For a finite group $G$, the following are equivalent:

<v-clicks>

- $G$ is nilpotent.
- Every Sylow subgroup of $G$ is normal.
- $G$ is the direct product of its Sylow subgroups:

</v-clicks>

<v-click>

$$
G\cong \prod_{p\mid |G|} P_p.
$$

</v-click>

<v-click>

Here $P_p$ denotes the Sylow $p$-subgroup of $G$.

</v-click>

---

# Nilpotent Implies Solvable

The lower central series is

$$
\gamma_1(G)=G,
\qquad
\gamma_{i+1}(G)=[\gamma_i(G),G].
$$

<v-click>

The derived series satisfies

$$
G^{(m)}\le \gamma_{2^m}(G).
$$

</v-click>

<v-click>

So if $\gamma_{c+1}(G)=1$, then $G^{(m)}=1$ once $2^m>c$.

</v-click>

<v-click>

Thus:

$$
\boxed{\text{nilpotent}\Longrightarrow\text{solvable}.}
$$

</v-click>

---

# Converse Fails

$S_3$ is solvable:

$$
1\triangleleft A_3\triangleleft S_3,
\qquad
A_3\cong\mathbb Z_3,\quad S_3/A_3\cong\mathbb Z_2.
$$

<v-click>

$S_3$ is not nilpotent.

For finite nilpotent groups, every Sylow subgroup is normal.

</v-click>

<v-click>

The Sylow $2$-subgroups of $S_3$ have order $2$, and

$$
n_2=3.
$$

Hence no Sylow $2$-subgroup is normal.

</v-click>

---
layout: center
---

# Part V

## Summary Criteria

---

# Implication Diagram

<div class="grid grid-cols-[0.95fr_1.05fr] gap-8 items-center">

<div style="font-size: 0.9rem;">

The inclusions are strict:

<v-clicks>

- $D_4$ is nilpotent but not abelian.
- $S_3$ is solvable but not nilpotent.
- $A_5$ is not solvable.

</v-clicks>

</div>

<div>
  <img src="/group-hierarchy.svg" style="height: 350px; margin: 0 auto;" />
</div>

</div>

---

# Example Table

<div style="font-size: 0.78rem;">

| Group | Composition factors | Solvable? | Nilpotent? |
|---|---|---|---|
| $\mathbb Z_n$ | $\mathbb Z_p$ with multiplicity $v_p(n)$ | yes | yes |
| $D_4$ | three copies of $\mathbb Z_2$ | yes | yes |
| $S_3$ | $\mathbb Z_3,\mathbb Z_2$ | yes | no |
| $A_5$ | $A_5$ | no | no |

</div>

<v-click>

$A_5$ is non-abelian simple.

</v-click>

---

# Criteria for Solvability

For a finite group $G$, any of the following proves solvability:

<v-clicks>

- Find a subnormal series with abelian factors.
- Compute the derived series and show it reaches $1$.
- Show all composition factors are cyclic of prime order.
- Use known closure properties: subgroups, quotients, extensions of solvable groups are solvable.

</v-clicks>

<v-click>

To prove non-solvability, it is enough to exhibit a non-abelian simple composition factor.

</v-click>

---

# Criteria for Nilpotence

For a finite group $G$, any of the following proves nilpotence:

<v-clicks>

- Build the upper central series until it reaches $G$.
- Build the lower central series until it reaches $1$.
- If $G$ is finite, check whether every Sylow subgroup is normal.
- If $G$ is a finite $p$-group, conclude immediately that it is nilpotent.

</v-clicks>

<v-click>

To prove non-nilpotence, it is enough to find a non-normal Sylow subgroup.

</v-click>

---

# Comparison

<div style="font-size: 0.83rem;">

| Notion | Criterion for finite groups |
|---|---|
| composition factors | simple factors in a composition series |
| solvable | all composition factors are $\mathbb Z_p$ |
| nilpotent | all Sylow subgroups are normal |

</div>

<v-click>

The implications are

$$
\text{abelian}\Longrightarrow\text{nilpotent}\Longrightarrow\text{solvable}.
$$

</v-click>

<v-click>

The reverse implications are false:

$$
D_4\text{ is nilpotent but not abelian},
\qquad
S_3\text{ is solvable but not nilpotent}.
$$

</v-click>

---

# False Statements

<div style="font-size: 0.9rem;">

1. "A subnormal series must be a normal series."

<v-click>

False: subnormal only requires $G_{i+1}\triangleleft G_i$.

</v-click>

<v-click>

2. "Composition factors determine the group."

</v-click>

<v-click>

False: $\mathbb Z_4$ and $\mathbb Z_2\times\mathbb Z_2$ have the same composition factors.

</v-click>

<v-click>

3. "Solvable implies nilpotent."

</v-click>

<v-click>

False: $S_3$ is solvable but not nilpotent.

</v-click>

</div>

---
layout: center
---

# Summary

---

# What to Remember

<div style="font-size: 0.84rem;">

1. A subnormal series decomposes a group into factor groups $G_i/G_{i+1}$.

2. A composition series is a fully refined subnormal series; Jordan-Holder says its simple factors are well-defined up to order.

3. For $f\in\mathbb Q[x]$, solvability by radicals is equivalent to solvability of its Galois group.

4. For finite groups, solvable iff all composition factors are cyclic groups $\mathbb Z_p$.

5. The derived series is the standard criterion for solvability in examples.

6. $G$ is nilpotent iff $Z_c(G)=G$ for some $c$, equivalently iff $\gamma_{c+1}(G)=1$ for some $c$.

7. A finite group is nilpotent iff it is the direct product of its Sylow subgroups.

The implication chain is

$$
\text{abelian}\Longrightarrow\text{nilpotent}\Longrightarrow\text{solvable}\Longrightarrow\text{group}.
$$

</div>
