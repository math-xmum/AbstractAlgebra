---
title: "MAT205: Abstract Algebra II - Rings, Polynomial Rings, and Polynomial Functions"
math: katex
---

# MAT205: Abstract Algebra II

## Rings, Polynomial Rings, and Polynomial Functions

<br/>

**Ma, Jia-Jun** - Xiamen University Malaysia

---
layout: center
---

# Part I

## Rings and Ring Homomorphisms

---

# Definition: Ring

**Definition.** A **ring** $R$ is a set with two binary operations

$$
+:R\times R\to R,\qquad \cdot:R\times R\to R
$$

such that:

<v-clicks>

1. $(R,+)$ is an abelian group;

2. multiplication is associative;

3. multiplication distributes over addition:

</v-clicks>

<v-click>

$$
a(b+c)=ab+ac,\qquad (a+b)c=ac+bc.
$$

</v-click>

<v-click>

The additive identity is written $0$.

</v-click>

---

# Example: Basic Rings

<div style="font-size: 0.96rem;">

| Ring | Comment |
|---|---|
| $\mathbb Z$ | integers |
| $\mathbb Q,\mathbb R,\mathbb C$ | fields |
| $\mathbb Z_n$ | modular arithmetic |
| $M_n(F)$ | matrices over a field |
| $\mathcal F(\mathbb R,\mathbb R)$ | real-valued functions |
| $R_1\times R_2$ | product ring |

</div>

<v-click>

In $M_n(F)$, multiplication is usually not commutative.

</v-click>

---

# Definition: Commutative Rings and Unity

**Commutative ring.**

$$
ab=ba\qquad\text{for all }a,b\in R.
$$

<v-click>

**Ring with unity.** There is an element $1_R$ such that

$$
1_Ra=a1_R=a.
$$

</v-click>

<v-click>

For most of this course, our default examples are commutative rings with unity.

</v-click>

---

# Definition: Units

Let $R$ be a ring with unity.

<v-click>

An element $u\in R$ is a **unit** if there exists $v\in R$ such that

$$
uv=vu=1_R.
$$

</v-click>

<v-click>

The units form a group:

$$
R^\times.
$$

</v-click>

<v-click>

Examples:

$$
\mathbb Z^\times=\{\pm1\},\qquad
\mathbb Q^\times=\mathbb Q\setminus\{0\}.
$$

</v-click>

---

# Definition: Fields

**Definition.** A **field** is a commutative ring with unity $1\ne0$ in which every nonzero element is a unit.

<v-click>

Examples:

$$
\mathbb Q,\qquad \mathbb R,\qquad \mathbb C,\qquad \mathbb F_p=\mathbb Z_p.
$$

</v-click>

<v-click>

Non-example:

$$
\mathbb Z
$$

is not a field, because $2$ has no inverse in $\mathbb Z$.

</v-click>

---

# Definition: Zero Divisors

**Definition.** A nonzero element $a\in R$ is a **zero divisor** if there exists nonzero $b\in R$ such that

$$
ab=0.
$$

<v-click>

Example in $\mathbb Z_6$:

$$
\bar 2\cdot \bar 3=\bar 0.
$$

</v-click>

<v-click>

So $\mathbb Z_6$ has zero divisors.

</v-click>

---

# Definition: Integral Domains

A ring has **no zero divisors** if

$$
ab=0\quad\Longrightarrow\quad a=0\text{ or }b=0.
$$

<v-click>

A commutative ring with unity $1\ne0$ and no zero divisors is an **integral domain**.

</v-click>

<v-click>

Examples:

$$
\mathbb Z,\qquad F,\qquad F[x],\qquad F[x_1,\dots,x_n],\qquad F[t,t^{-1}].
$$

</v-click>

---

# Example: More Zero Divisors

Product rings usually have zero divisors:

$$
(1,0)(0,1)=(0,0)
\quad\text{in }R\times S.
$$

<v-click>

Matrix rings have zero divisors:

$$
\begin{pmatrix}1&0\\0&0\end{pmatrix}
\begin{pmatrix}0&0\\0&1\end{pmatrix}
=
\begin{pmatrix}0&0\\0&0\end{pmatrix}.
$$

</v-click>

<v-click>

Quotient rings can have nilpotents:

$$
\bar x^2=0\quad\text{in }F[x]/(x^2).
$$

</v-click>

---

# Definition: Ring Homomorphisms

Let $R,S$ be rings.

<v-click>

**Definition.** A map $\varphi:R\to S$ is a **ring homomorphism** if

$$
\varphi(a+b)=\varphi(a)+\varphi(b),
$$

and

$$
\varphi(ab)=\varphi(a)\varphi(b).
$$

</v-click>

<v-click>

Modern convention often also requires

$$
\varphi(1_R)=1_S.
$$

</v-click>

---

# Proposition: Kernels Are Ideals

Let $\varphi:R\to S$ be a ring homomorphism. Then

$$
\ker\varphi=\{r\in R:\varphi(r)=0\}
$$

is an ideal of $R$.

<v-click>

Example:

$$
\pi:\mathbb Z\to\mathbb Z_n,\qquad a\mapsto \bar a,
\qquad \ker\pi=n\mathbb Z.
$$

</v-click>

<v-click>

This is the guiding model for quotient rings:

$$
\mathbb Z_n\simeq \mathbb Z/n\mathbb Z.
$$

</v-click>

---

# Proposition: Point Evaluation of Functions

Let

$$
\mathcal F(\mathbb R,\mathbb R)=\{f:\mathbb R\to\mathbb R\}.
$$

Use pointwise operations:

$$
(f+g)(x)=f(x)+g(x),\qquad (fg)(x)=f(x)g(x).
$$

<v-click>

For each $a\in\mathbb R$, the map

$$
\operatorname{ev}_a:\mathcal F(\mathbb R,\mathbb R)\to\mathbb R,\qquad f\mapsto f(a).
$$

is a ring homomorphism.

</v-click>

---

# Example: Additive Isomorphism Need Not Preserve Multiplication

As abelian groups,

$$
\mathbb Z\simeq 2\mathbb Z
$$

by

$$
\phi(x)=2x.
$$

<v-click>

But this is not a ring homomorphism:

$$
\phi(xy)=2xy,
\qquad
\phi(x)\phi(y)=4xy.
$$

</v-click>

<v-click>

A ring homomorphism must preserve both addition and multiplication.

</v-click>

---
layout: center
---

# Part II

## Ideals and Quotient Rings

---

# Example: Historical Motivation for Ideals

<div style="display: grid; grid-template-columns: 1fr 250px; gap: 2rem; align-items: start;">

<div>

Kummer introduced **ideal numbers** while studying Fermat's Last Theorem.

<v-click>

The obstruction was failure of unique factorization in some rings of algebraic integers.

</v-click>

<v-click>

Dedekind later replaced ideal numbers by **ideals**:

$$
\text{subsets that behave like generalized multiples.}
$$

</v-click>

<v-click>

For us today:

$$
\boxed{\text{ideals are the right kernels for ring homomorphisms}.}
$$

</v-click>

</div>

<div>
  <img src="/ernst-eduard-kummer.jpg" style="height: 250px; width: 190px; object-fit: cover; border: 1px solid #bbb; border-radius: 6px; margin: 0 auto;" />
  <div style="font-size: 0.72rem; margin-top: 0.4rem; text-align: center; opacity: 0.72;">Ernst Eduard Kummer</div>
</div>

</div>

---

# Definition: Ideals

Let $R$ be a commutative ring.

<v-click>

**Definition.** An **ideal** $I\subseteq R$ is a subset such that:

</v-click>

<v-clicks>

1. $I$ is an additive subgroup of $(R,+)$;

2. for every $r\in R$ and every $a\in I$,

$$
ra\in I.
$$

</v-clicks>

<v-click>

If $I\ne R$, then $I$ is a **proper ideal**.

</v-click>

<v-click>

Slogan:

$$
\boxed{\text{ideals are kernels of ring homomorphisms}.}
$$

</v-click>

---

# Definition: Principal Ideals

Let $R$ be a commutative ring and $a\in R$.

<v-click>

The **principal ideal generated by $a$** is

$$
(a)=Ra=\{ra:r\in R\}.
$$

</v-click>

<v-click>

Examples:

$$
(n)=n\mathbb Z\subset\mathbb Z,
\qquad
(x-a)\subset F[x].
$$

</v-click>

<v-click>

This notation also appears inside quotient rings such as $\mathbb Z_n$.

</v-click>

<v-click>

Whenever $I$ is an ideal, we can form the quotient ring $R/I$.

</v-click>

---

# Definition: Principal Ideal Domains

Let $D$ be an integral domain.

<v-click>

A **principal ideal domain**, or **PID**, is an integral domain in which every ideal is principal.

</v-click>

<v-click>

That is, for every ideal $I\subseteq D$, there exists $a\in D$ such that

$$
I=(a).
$$

</v-click>

<v-click>

Examples:

$$
\mathbb Z,\qquad F[x].
$$

</v-click>

<v-click>

A typical non-example is

$$
F[x,y],
$$

where the ideal $(x,y)$ is not principal.

</v-click>

---

# Definition: Quotient Rings

Let $I\subseteq R$ be an ideal.

<v-click>

The quotient ring $R/I$ is the set of cosets

$$
r+I=\{r+i:i\in I\}.
$$

</v-click>

<v-click>

Addition and multiplication are defined by

$$
(r+I)+(s+I)=(r+s)+I,
$$

$$
(r+I)(s+I)=rs+I.
$$

</v-click>

<v-click>

The quotient map

$$
\pi:R\to R/I,\qquad r\mapsto r+I
$$

is a ring homomorphism with $\ker\pi=I$.

</v-click>

---

# Example: Quotient Rings

For $n\ge1$,

$$
\mathbb Z/n\mathbb Z\simeq \mathbb Z_n.
$$

<v-click>

The coset $a+n\mathbb Z$ corresponds to $\bar a$.

</v-click>

<v-click>

In polynomial rings,

$$
F[x]/(x-a)\simeq F
$$

by evaluation at $a$.

</v-click>

---

# Proposition: Ideals in $\mathbb Z_n$

Ideals of $\mathbb Z_n$ correspond to divisors of $n$.

<v-click>

For $d\mid n$,

$$
(d)=d\mathbb Z_n=\{\bar0,\bar d,\overline{2d},\dots\}.
$$

</v-click>

<v-click>

Every ideal of $\mathbb Z_n$ has this form.

</v-click>

<v-click>

The larger $d$ is, the smaller $(d)$ is.

</v-click>

---

# Example: Ideals of $\mathbb Z_{12}$

The divisors of $12$ are

$$
1,\quad 2,\quad 3,\quad 4,\quad 6,\quad 12.
$$

<v-click>

So the ideals are

$$
(1),\quad (2),\quad (3),\quad (4),\quad (6),\quad (12).
$$

</v-click>

<v-click>

Question:

$$
\boxed{\text{Which of these are maximal? Which are prime?}}
$$

</v-click>

---

# Definition: Maximal Ideals

Let $R$ be a commutative ring with unity.

<v-click>

An ideal $\mathfrak m\subsetneq R$ is **maximal** if there is no ideal $I$ with

$$
\mathfrak m\subsetneq I\subsetneq R.
$$

</v-click>

<v-click>

Key test:

$$
\boxed{\mathfrak m\text{ is maximal}
\quad\Longleftrightarrow\quad
R/\mathfrak m\text{ is a field}.}
$$

</v-click>

---

# Definition: Prime Ideals

Let $R$ be a commutative ring with unity.

<v-click>

An ideal $\mathfrak p\subsetneq R$ is **prime** if

$$
ab\in\mathfrak p
\quad\Longrightarrow\quad
a\in\mathfrak p\text{ or }b\in\mathfrak p.
$$

</v-click>

<v-click>

Key test:

$$
\boxed{\mathfrak p\text{ is prime}
\quad\Longleftrightarrow\quad
R/\mathfrak p\text{ is an integral domain}.}
$$

</v-click>

<v-click>

Always:

$$
\text{maximal}\Longrightarrow \text{prime}.
$$

</v-click>

---

# Example: Maximal Ideals in $\mathbb Z_{12}$

In $\mathbb Z_{12}$:

$$
(2)\quad\text{and}\quad (3)
$$

are maximal.

<v-click>

Indeed,

$$
\mathbb Z_{12}/(2)\simeq\mathbb Z_2,\qquad
\mathbb Z_{12}/(3)\simeq\mathbb Z_3.
$$

</v-click>

<v-click>

They are also prime.

</v-click>

<v-click>

In general:

$$
(d)\subset\mathbb Z_n\text{ is maximal}
\quad\Longleftrightarrow\quad
n/d\text{ is prime}.
$$

</v-click>

---

# Proposition: Ideals in $F[x]$

For $a\in F$,

$$
(x-a)\subset F[x]
$$

is maximal because

$$
F[x]/(x-a)\simeq F.
$$

<v-click>

More generally, if $p(x)\in F[x]$ is irreducible, then

$$
(p(x))
$$

is maximal.

</v-click>

---

# Example: Prime But Not Maximal

In a commutative ring with unity:

$$
\text{maximal}\Longrightarrow\text{prime}.
$$

<v-click>

But prime need not imply maximal.

</v-click>

<v-click>

Example:

$$
(x)\subset F[x,y].
$$

</v-click>

<v-click>

Since

$$
F[x,y]/(x)\simeq F[y],
$$

$(x)$ is prime but not maximal.

</v-click>

---

# Example: Point Ideals in $F[x,y]$

For a point $(a,b)\in F^2$,

$$
\mathfrak m_{(a,b)}=(x-a,y-b).
$$

<v-click>

This is maximal because

$$
F[x,y]/(x-a,y-b)\simeq F.
$$

</v-click>

<v-click>

Geometric meaning:

$$
(x-a,y-b)=\text{polynomials vanishing at }(a,b).
$$

</v-click>

---

# Definition: Radical of an Ideal

Let $I\subseteq R$ be an ideal in a commutative ring.

<v-click>

The **radical** of $I$ is

$$
\sqrt I=\{r\in R:r^n\in I\text{ for some }n\ge1\}.
$$

</v-click>

<v-click>

If $\sqrt I=I$, then $I$ is a **radical ideal**.

</v-click>

<v-click>

The radical $\sqrt I$ is again an ideal.

</v-click>

---

# Definition: Nilradical

The radical of the zero ideal is the **nilradical**:

$$
\sqrt{(0)}
=
\{r\in R:r^n=0\text{ for some }n\ge1\}.
$$

<v-click>

It is the set of nilpotent elements of $R$.

</v-click>

---

# Example: Radical Ideals

In $F[x]$:

$$
\sqrt{((x-a)^m)}=(x-a).
$$

<v-click>

In $F[x,y]$:

$$
\sqrt{(x^2,y)}=(x,y).
$$

</v-click>

<v-click>

Radical removes repeated or nilpotent behavior.

</v-click>

---

# Example: Radical in $\mathbb Z_{12}$

In $\mathbb Z_{12}$,

$$
\sqrt{(4)}=(2).
$$

<v-click>

Reason:

$$
\bar2^2=\bar4\in(4),
$$

so $\bar2\in\sqrt{(4)}$.

</v-click>

<v-click>

This is another way nilpotent-like behavior appears in quotient rings.

</v-click>

---
layout: center
---

# Part III

## Polynomial Rings

---

# Definition: Polynomial Rings

Let $R$ be a commutative ring with unity.

<v-click>

The polynomial ring over $R$ is

$$
R[x]=\{a_0+a_1x+\cdots+a_nx^n:a_i\in R\}.
$$

</v-click>

<v-click>

The symbol $x$ is an **indeterminate**, not an element of $R$.

</v-click>

<v-click>

The inclusion $R\to R[x]$ sends $r$ to the constant polynomial $r$.

</v-click>

---

# Definition: Formal Polynomial Viewpoint

A polynomial can be modeled as a formal sum

$$
\sum_{i=0}^{\infty}a_ix^i
$$

where all but finitely many $a_i$ are zero.

<v-click>

This avoids ambiguity:

$$
1+x
=
1+x+0x^2
=
1+x+0x^2+0x^3+\cdots.
$$

</v-click>

---

# Definition: Addition in $R[x]$

Add coefficients:

$$
(a_0+a_1x+\cdots)+(b_0+b_1x+\cdots)
$$

$$
=(a_0+b_0)+(a_1+b_1)x+\cdots.
$$

<v-click>

Example in $\mathbb Z_5[x]$:

$$
(3x^2+4x+1)+(4x^2+2)
=2x^2+4x+3.
$$

</v-click>

---

# Definition: Multiplication in $R[x]$

Let

$$
f=\sum_{i=0}^m a_ix^i,\qquad g=\sum_{j=0}^n b_jx^j.
$$

<v-click>

The product is

$$
fg=\sum_{k=0}^{m+n} c_kx^k,
$$

where

$$
c_k=\sum_{i+j=k}a_ib_j.
$$

</v-click>

<v-click>

This is the usual distributive multiplication:

$$
(a_ix^i)(b_jx^j)=a_ib_jx^{i+j}.
$$

</v-click>

---

# Example: Multiplication Depends on $R$

Multiply as usual, using coefficients in $F$:

$$
(x+1)(x^2+2)=x^3+x^2+2x+2.
$$

<v-click>

In $\mathbb Z_2[x]$:

$$
(x+1)^2=x^2+2x+1=x^2+1.
$$

</v-click>

<v-click>

The coefficient ring matters.

</v-click>

---

# Lemma: Degree over Domains

Let $D$ be an integral domain.

<v-click>

For a nonzero polynomial

$$
f(x)=a_nx^n+\cdots+a_1x+a_0,\qquad a_n\ne0,
$$

the **degree** is

$$
\deg f=n.
$$

</v-click>

<v-click>

If $f,g\in D[x]$ are nonzero, then

$$
\deg(fg)=\deg f+\deg g.
$$

</v-click>

---

# Proposition: Polynomial Rings Preserve Domains

Let $D$ be an integral domain.

<v-click>

Then $D[x]$ is an integral domain.

</v-click>

<v-click>

Indeed, if $0\ne f,g\in D[x]$, then

$$
\deg(fg)=\deg f+\deg g.
$$

</v-click>

<v-click>

So $fg\ne0$.

$$
\boxed{D[x]\text{ has no zero divisors}.}
$$

</v-click>

---

# Proposition: Units in $F[x]$

Let $F$ be a field.

<v-click>

The units are exactly the nonzero constants:

$$
F[x]^\times=F^\times.
$$

Indeed, if $f(x)g(x)=1$, then $\deg f+\deg g=0$.

</v-click>

<v-click>

In particular, $F[x]$ is not a field, because $x$ has no inverse.

</v-click>

---

# Counterexample: Zero Divisors in $R[x]$

If the coefficient ring has zero divisors, then the polynomial ring does too.

<v-click>

In $\mathbb Z_6$:

$$
\bar 2\cdot\bar 3=\bar0.
$$

</v-click>

<v-click>

So in $\mathbb Z_6[x]$:

$$
(2x+2)(3x+3)=0.
$$

</v-click>

<v-click>

The good behavior of $F[x]$ comes from no zero divisors in $F$.

</v-click>

---

# Definition: Multivariable Polynomial Rings

For a commutative ring with unity $R$,

$$
R[x_1,\dots,x_n]
$$

is the ring of finite $R$-linear combinations of monomials

$$
x_1^{a_1}\cdots x_n^{a_n}.
$$

<v-click>

For example,

$$
R[x,y]=(R[x])[y].
$$

</v-click>

---
layout: center
---

# Part IV

## Algebras, Free Algebras, and Evaluation

---

# Definition: $R$-Modules

Let $R$ be a commutative ring with unity.

<v-click>

An **$R$-module** is an abelian group $M$ with scalar multiplication

$$
R\times M\to M,\qquad (r,m)\mapsto rm,
$$

such that

$$
(r+s)m=rm+sm,\quad r(m+n)=rm+rn,
$$

$$
(rs)m=r(sm),\qquad 1m=m.
$$

</v-click>

<v-click>

Examples: vector spaces, $R^n$, and ideals $I\subseteq R$.

</v-click>

---

# Definition: $R$-Algebras

Let $R$ be a commutative ring with unity.

<v-click>

A **commutative $R$-algebra** is a commutative ring $A$ with unity together with a unital ring homomorphism

$$
R\to A.
$$

</v-click>

<v-click>

Convention: after choosing this map, we write elements of $R$ as scalars in $A$.

</v-click>

<v-click>

Then $A$ is an $R$-module by

$$
r\cdot a=ra.
$$

</v-click>

<v-click>

Examples:

$$
R,\qquad R[x],\qquad R[x_1,\dots,x_n],\qquad F\le E.
$$

</v-click>

---

# Definition: $R$-Algebra Homomorphisms

Let $A$ and $B$ be commutative $R$-algebras.

<v-click>

An **$R$-algebra homomorphism** is a unital ring homomorphism $\varphi:A\to B$ such that

$$
\varphi(r)=r\qquad(r\in R),
$$

using the scalar convention in both $A$ and $B$.

</v-click>

<v-click>

Equivalently, $\varphi$ fixes the scalars from $R$.

</v-click>

---

# Theorem: Universal Property of Polynomial Algebras

Let $R[x_s\mid s\in S]$ be the polynomial ring whose variables are indexed by $S$.

<v-click>

Its elements are finite $R$-linear combinations of finite monomials

$$
r\,x_{s_1}^{e_1}\cdots x_{s_m}^{e_m}.
$$

</v-click>

<v-click>

Let

$$
i:S\to R[x_s\mid s\in S],\qquad s\mapsto x_s.
$$

</v-click>

<v-click>

For every commutative $R$-algebra $A$, precomposition with $i$ gives a bijection

$$
i^\ast:\operatorname{Hom}_{R\text{-alg}}\!\left(R[x_s\mid s\in S],A\right)
\longrightarrow \operatorname{Map}(S,A).
$$

</v-click>

---

# Corollary: Polynomial Algebras Are Free

The universal property says:

<v-click>

every set map $a:S\to A$ extends uniquely to an $R$-algebra homomorphism

$$
\Phi_a:R[x_s\mid s\in S]\to A.
$$

</v-click>

<v-click>

This is what it means to say:

$$
R[x_s\mid s\in S]
$$

is the **free commutative $R$-algebra on the set $S$**.

</v-click>

<v-click>

In particular, $R[x]$ is free on one generator, and $R[x_1,\dots,x_n]$ is free on $n$ generators.

</v-click>

---

# Proof: Polynomial Rings Are Free

Given a set map $a:S\to A$, define $\Phi_a$ by

$$
\Phi_a(x_s)=a(s),\qquad \Phi_a(r)=r.
$$

<v-click>

On a monomial,

$$
\Phi_a\!\left(r\,x_{s_1}^{e_1}\cdots x_{s_m}^{e_m}\right)
=r\,a(s_1)^{e_1}\cdots a(s_m)^{e_m}.
$$

</v-click>

<v-click>

Extend by finite sums. This gives an $R$-algebra homomorphism because multiplication of monomials corresponds to adding exponents.

</v-click>

<v-click>

Uniqueness: every polynomial is built from scalars, addition, multiplication, and the generators $x_s$.

</v-click>

---

# Definition: Evaluation Homomorphism

Let $A$ be a commutative $R$-algebra and let $a:S\to A$ be a set map.

<v-click>

The unique homomorphism

$$
\operatorname{ev}_a:R[x_s\mid s\in S]\to A,\qquad x_s\mapsto a(s)
$$

is called the **evaluation homomorphism** at $a$.

</v-click>

<v-click>

If $S=\{1,\dots,n\}$, then $a:S\to A$ is the same data as a tuple

$$
(a_1,\dots,a_n)\in A^n,
$$

and

$$
\operatorname{ev}_a:R[x_1,\dots,x_n]\to A,\qquad x_i\mapsto a_i.
$$

</v-click>

---

# Definition: Polynomial Functions from Evaluation

Let $A$ be a commutative $R$-algebra.

<v-click>

For $f\in R[x_1,\dots,x_n]$, the **polynomial function defined by $f$ on $A$** is

$$
f_A:A^n\to A,\qquad
(a_1,\dots,a_n)\mapsto \operatorname{ev}_{(a_1,\dots,a_n)}(f).
$$

</v-click>

<v-click>

In one variable, if $f=r_0+r_1x+\cdots+r_dx^d$, then

$$
\operatorname{ev}_a(f)=r_0+r_1a+\cdots+r_da^d.
$$

</v-click>

---

# Proposition: Evaluation Preserves Operations

Let $A$ be a commutative $R$-algebra and let $a:S\to A$.

<v-click>

For $f,g\in R[x_s\mid s\in S]$,

$$
\operatorname{ev}_a(f+g)=\operatorname{ev}_a(f)+\operatorname{ev}_a(g),
$$

</v-click>

<v-click>

$$
\operatorname{ev}_a(fg)=\operatorname{ev}_a(f)\operatorname{ev}_a(g).
$$

</v-click>

<v-click>

This is not an extra calculation: it is exactly the statement that $\operatorname{ev}_a$ is an $R$-algebra homomorphism.

</v-click>

---

# Example: A Point Ideal in Two Variables

Take $R=A=F$ and the point $(2,3)\in F^2$.

<v-click>

The evaluation map is

$$
\operatorname{ev}_{(2,3)}:F[x,y]\to F,\qquad x\mapsto2,\quad y\mapsto3.
$$

</v-click>

<v-click>

Its kernel is the point ideal

$$
(x-2,y-3).
$$

</v-click>

<v-click>

This is the multivariable analogue of $\ker(\operatorname{ev}_a)=(x-a)$.

</v-click>

---
layout: center
---

# Part V

## Division, Kernels, and Root Bounds

---

# Definition: Zeros

Let $F\le E$, let $\alpha\in E$, and let $f\in F[x]$.

<v-click>

The element $\alpha$ is a **zero** of $f$ if

$$
\operatorname{ev}_{\alpha}(f)=0.
$$

</v-click>

<v-click>

Equivalently, if $f_E:E\to E$ is the polynomial function defined by $f$, then

$$
f_E(\alpha)=0.
$$

</v-click>

---

# Example: Computing Zeros

In $\mathbb Q[x]$, let

$$
f=x^2+x-6.
$$

<v-click>

Then

$$
f_{\mathbb R}(2)=2^2+2-6=0.
$$

</v-click>

<v-click>

Thus $2$ is a zero of $f$ over $\mathbb R$.

</v-click>

<v-click>

$$
x^2+1\in\mathbb Q[x]
$$

has zero $i$ over $\mathbb C$, but not over $\mathbb Q$.

</v-click>

---

# Theorem: Division Algorithm

Let $R$ be a commutative ring with unity.

<v-click>

If $g\in R[x]$ has leading coefficient a unit, then for every $f\in R[x]$ there exist unique $q,r\in R[x]$ such that

$$
f=qg+r,\qquad r=0\text{ or }\deg r<\deg g.
$$

</v-click>

<v-click>

In particular, division by any **monic** polynomial works over any commutative ring.

</v-click>

---

# Proof: Division by a Monic Polynomial

Let $g=x^d+\text{lower terms}$.

<v-click>

If $\deg f=m\ge d$ and the leading term of $f$ is $cx^m$, subtract

$$
cx^{m-d}g.
$$

</v-click>

<v-click>

This cancels the leading term of $f$ and lowers the degree.

</v-click>

<v-click>

Repeating gives $f=qg+r$ with $\deg r<d$.

</v-click>

<v-click>

Uniqueness follows because multiplying by a monic polynomial raises degree by $d$.

</v-click>

---

# Theorem: Kernel of Evaluation

Let $R$ be a commutative ring with unity and let $a\in R$.

$$
\operatorname{ev}_a:R[x]\to R
$$

<v-click>

Then

$$
\boxed{\ker(\operatorname{ev}_a)=(x-a).}
$$

</v-click>

---

# Proof: Kernel of Evaluation

By division by the monic polynomial $x-a$, write

$$
f=q(x)(x-a)+r
$$

with $r\in R$.

<v-click>

Evaluating at $a$ gives

$$
f(a)=q(a)(a-a)+r=r.
$$

</v-click>

<v-click>

So $f\in\ker(\operatorname{ev}_a)$ if and only if $r=0$.

</v-click>

<v-click>

This is exactly $f\in(x-a)$.

</v-click>

---

# Corollary: Factor Theorem

Let $R$ be a commutative ring with unity, $a\in R$, and $f\in R[x]$.

<v-click>

Then

$$
f(a)=0
\quad\Longleftrightarrow\quad
f\in(x-a).
$$

</v-click>

<v-click>

$$
\boxed{a\text{ is a zero of }f
\quad\Longleftrightarrow\quad
x-a\text{ divides }f.}
$$

</v-click>

---

# Lemma: Root Ideals over a Field

Let $F$ be a field and let $a_i\ne a_j$ in $F$.

<v-click>

Then

$$
(x-a_i)+(x-a_j)=F[x].
$$

</v-click>

<v-click>

Indeed,

$$
(x-a_i)-(x-a_j)=a_j-a_i\in F^\times.
$$

</v-click>

<v-click>

So $1\in (x-a_i)+(x-a_j)$.

</v-click>

---

# Lemma: Comaximal Ideals

Let $I,J$ be ideals in a commutative ring $R$.

<v-click>

If $I+J=R$, then

$$
I\cap J=IJ.
$$

</v-click>

<v-click>

More generally, if $I_1,\dots,I_k$ are pairwise comaximal, then

$$
\bigcap_{i=1}^k I_i=\prod_{i=1}^k I_i.
$$

</v-click>

---

# Proof: Comaximal Ideals

It is always true that

$$
IJ\subseteq I\cap J.
$$

<v-click>

For the reverse inclusion, choose $u\in I$ and $v\in J$ with

$$
u+v=1.
$$

</v-click>

<v-click>

If $x\in I\cap J$, then

$$
x=x(u+v)=xu+xv.
$$

</v-click>

<v-click>

Here $xu\in JI=IJ$ and $xv\in IJ$, so $x\in IJ$.

</v-click>

---

# Proof: Pairwise Comaximal Case

Assume $I_1,\dots,I_k$ are pairwise comaximal.

<v-click>

By induction, set

$$
P=\prod_{i=1}^{k-1}I_i=\bigcap_{i=1}^{k-1}I_i.
$$

</v-click>

<v-click>

For each $i<k$, choose

$$
u_i\in I_i,\qquad v_i\in I_k,\qquad u_i+v_i=1.
$$

</v-click>

<v-click>

Expanding $\prod_{i<k}(u_i+v_i)=1$ shows

$$
1\in P+I_k.
$$

</v-click>

<v-click>

Thus

$$
\bigcap_{i=1}^k I_i=P\cap I_k=PI_k=\prod_{i=1}^k I_i.
$$

</v-click>

---

# Theorem: Root Bound over a Field

Let $F$ be a field and let $0\ne f\in F[x]$ have degree $n$.

<v-click>

Then $f$ has at most $n$ zeros in $F$.

</v-click>

<v-click>

Ideal translation:

$$
a\text{ is a zero of }f
\quad\Longleftrightarrow\quad
(f)\subseteq(x-a).
$$

</v-click>

---

# Proof: Root Bound over a Field

Suppose $a_1,\dots,a_k$ are distinct zeros of $f$.

<v-click>

Then

$$
f\in\bigcap_{i=1}^k(x-a_i).
$$

</v-click>

<v-click>

The ideals $(x-a_i)$ are pairwise comaximal, so

$$
\bigcap_{i=1}^k(x-a_i)
=
\prod_{i=1}^k(x-a_i)
=
\left(\prod_{i=1}^k(x-a_i)\right).
$$

</v-click>

<v-click>

Hence $\prod_i(x-a_i)\mid f$, so $k\le \deg f$.

</v-click>

---

# Definition: Fraction Field

Let $D$ be an integral domain.

<v-click>

The **fraction field** of $D$ is

$$
\operatorname{Frac}(D)
=\left\{\frac{a}{b}:a,b\in D,\ b\ne0\right\}/\sim,
$$

where

$$
\frac{a}{b}=\frac{c}{d}
\quad\Longleftrightarrow\quad
ad=bc.
$$

</v-click>

<v-click>

There is an injective ring homomorphism

$$
D\hookrightarrow \operatorname{Frac}(D),\qquad a\mapsto \frac{a}{1}.
$$

</v-click>

---

# Example: Fraction Fields

The standard example is

$$
\operatorname{Frac}(\mathbb Z)=\mathbb Q.
$$

<v-click>

If $F$ is a field, then

$$
\operatorname{Frac}(F[x])=F(x),
$$

the field of rational functions.

</v-click>

<v-click>

This construction is possible because $D$ has no zero divisors.

</v-click>

---

# Corollary: Root Bound over Domains

Let $D$ be an integral domain and let $0\ne f\in D[x]$ have degree $n$.

<v-click>

Then $f$ has at most $n$ zeros in $D$.

</v-click>

<v-click>

Proof: embed $D$ into its fraction field $K=\operatorname{Frac}(D)$ and view $f$ in $K[x]$.

</v-click>

<v-click>

The field theorem applies in $K[x]$, so the same bound holds for zeros lying in $D$.

</v-click>

---

# Counterexample: Rings with Zero Divisors

In $\mathbb Z_{12}$,

$$
x^2-5x+6=(x-2)(x-3).
$$

<v-click>

But this degree $2$ polynomial has four zeros:

$$
2,\quad 3,\quad 6,\quad 11.
$$

</v-click>

<v-click>

In $\mathbb Z_6$,

$$
x^2-x=x(x-1).
$$

The roots are

$$
0,\quad 1,\quad 3,\quad 4.
$$

</v-click>

<v-click>

Both examples have degree $2$ and four roots.

</v-click>

---
layout: center
---

# Part VI

## Local, Laurent, and Simple Rings

---

# Definition: Local Rings

**Definition.** A commutative ring with unity $R$ is **local** if it has a unique maximal ideal.

<v-click>

The main example today:

$$
F[x]_{(x-a)}
=
\left\{\frac{f(x)}{g(x)}:g(a)\ne0\right\}.
$$

</v-click>

<v-click>

Think:

$$
\text{rational functions defined at }a.
$$

</v-click>

---

# Proposition: The Maximal Ideal of $F[x]_{(x-a)}$

The unique maximal ideal is

$$
\mathfrak m_a
=
\left\{\frac{f(x)}{g(x)}:f(a)=0,\ g(a)\ne0\right\}.
$$

<v-click>

So

$$
\mathfrak m_a=\text{functions vanishing at }a.
$$

</v-click>

<v-click>

This is the local version of the ideal $(x-a)\subset F[x]$.

</v-click>

---

# Definition: Valuation as Order of Vanishing

For $0\ne f\in F[x]$, define

$$
v_a(f)=\max\{m:(x-a)^m\mid f(x)\}.
$$

<v-click>

We also set

$$
v_a(0)=\infty.
$$

</v-click>

<v-click>

Examples:

$$
v_0(x^3(x+1))=3,
$$

$$
v_2((x-2)^4(x+5))=4.
$$

</v-click>

---

# Proposition: Valuation Rules

The order of vanishing satisfies:

$$
v_a(fg)=v_a(f)+v_a(g),
$$

and

$$
v_a(f+g)\ge \min\{v_a(f),v_a(g)\}.
$$

<v-click>

This introduces valuation language.

</v-click>

---

# Definition: Laurent Polynomial Ring

The **Laurent polynomial ring** is

$$
F[t,t^{-1}]
=
\left\{\sum_{i=m}^n a_it^i:m,n\in\mathbb Z,\ a_i\in F\right\}.
$$

<v-click>

It is obtained from $F[t]$ by making $t$ invertible.

</v-click>

<v-click>

So it contains

$$
t^{-1},t^{-2},t^{-3},\dots.
$$

</v-click>

---

# Proposition: Units in $F[t,t^{-1}]$

The units are exactly

$$
F[t,t^{-1}]^\times
=
\{ct^n:c\in F^\times,\ n\in\mathbb Z\}.
$$

<v-click>

In particular, $t$ is a unit.

</v-click>

<v-click>

So

$$
(t)=F[t,t^{-1}].
$$

</v-click>

---

# Example: Maximal Ideals in $F[t,t^{-1}]$

For $a\in F^\times$, evaluation at $a$ gives

$$
F[t,t^{-1}]\to F,\qquad t\mapsto a.
$$

<v-click>

Its kernel is

$$
(t-a).
$$

</v-click>

<v-click>

But $a=0$ is not allowed, because $t^{-1}$ cannot be evaluated at $0$.

</v-click>

---

# Example: Valuation on Laurent Polynomials

For a nonzero Laurent polynomial, define $v_t$ as the lowest exponent of $t$, and set $v_t(0)=\infty$.

<v-click>

Example:

$$
v_t(3t^{-2}+5+t^4)=-2.
$$

</v-click>

<v-click>

Negative valuation means a pole at $t=0$.

</v-click>

---

# Definition: Simple Rings

A nonzero ring $R$ is **simple** if its only two-sided ideals are

$$
\{0\}\quad\text{and}\quad R.
$$

<v-click>

Analogy:

$$
\text{simple group}
\quad\leftrightarrow\quad
\text{simple ring}.
$$

</v-click>

---

# Example: Simple Rings

If $F$ is a field, then $F$ is a simple ring.

<v-click>

In commutative rings with unity:

$$
R\text{ simple}
\quad\Longleftrightarrow\quad
R\text{ is a field}.
$$

</v-click>

<v-click>

Noncommutative example:

$$
M_n(F)
$$

is simple as a ring, but not a field when $n\ge2$.

</v-click>
