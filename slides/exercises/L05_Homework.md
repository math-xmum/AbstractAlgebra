# MAT205 Lecture 5 Homework

Practice on free abelian groups, the classification of finitely generated abelian groups, and its invariants.

## Problem 1. Abelian Groups of Order 72

List all abelian groups of order $72$ up to isomorphism.

For each one, give both its invariant-factor decomposition
$$\mathbb{Z}/d_1 \oplus \mathbb{Z}/d_2 \oplus \cdots \oplus \mathbb{Z}/d_k, \qquad d_1 \mid d_2 \mid \cdots \mid d_k,$$
and its primary (prime-power) decomposition.

Hint: $72 = 2^3 \cdot 3^2$. Work prime by prime using partitions of $3$ and partitions of $2$.

## Problem 2. Free Rank Is an Invariant

Prove that $\mathbb{Z}^m \not\cong \mathbb{Z}^n \oplus T$ whenever $m > n$ and $T$ is a finite (torsion) abelian group.

Hint: tensor with $\mathbb{Q}$, or equivalently quotient by the torsion subgroup, to extract the free rank.

## Problem 3. Counting $d$-Torsion

Let $G \cong \mathbb{Z}/d_1 \oplus \cdots \oplus \mathbb{Z}/d_k$ be a finite abelian group in invariant-factor form, and for $d \geq 1$ set
$$G[d] \;=\; \{g \in G : d\,g = 0\}.$$

a. Prove that
$$|G[d]| \;=\; \prod_{i=1}^{k} \gcd(d, d_i).$$

Hint: work component by component and use the fact that in $\mathbb{Z}/m$, the elements killed by $d$ form the subgroup of order $\gcd(d, m)$.

b. Use the formula to count the number of elements of order exactly $4$ in
$$\mathbb{Z}/4 \oplus \mathbb{Z}/2 \oplus \mathbb{Z}/8.$$

Hint: elements of order exactly $4$ are those in $G[4]$ but not in $G[2]$.
