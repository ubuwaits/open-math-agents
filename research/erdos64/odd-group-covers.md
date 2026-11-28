# Power-of-two cycles in regular covers of the tetrahedron

Chad Mazzola (@ubuwaits), using Codex.

## A sharp bound for covers with a triangle

Suppose a finite group acts regularly on the sheets and every commutator of the group is central. If its tetrahedral cover contains a triangle, it contains a simple cycle of length 4, 8, 16 or 32. The Heisenberg covers below show that 32 is sharp. [Triangle theorem](Erdos64TriangleCovers.lean) · [Central-commutator proof](Erdos64ClassTwo.lean)

To see why a triangle helps, label its colors $0,3,1$, and identify all sheet sets by transport along the new spanning star at color 0. The triangle makes the chord $31$ act as the identity. Write $a,b$ for the left multipliers on $12$ and $23$, and $z=aba^{-1}b^{-1}$. This normalization accommodates all four positions of the projected triangle.

If $z^2=1$, its cyclic subgroup is normal and has at most two elements. The marked elements commute in the quotient. There is a simple 4-, 8- or 16-cycle there by the abelian result, and lifting through a normal two-group increases its length by a factor of at most two. [Lifting and abelian-quotient bounds](Erdos64NormalCovers.lean)

If $z^2\ne1$, the following single color sequence always gives a simple 32-cycle. In this case it suffices that $z$ commute with $a$ and $b$.

```text
01321021320120123021021023012012
```

Start on the identity sheet and return to color 0 after the final digit. In the integral Heisenberg cover the word closes, its horizontal coordinates $x,y$ stay in $[-2,0]$, and two distinct vertices of the same color and the same $x,y$ have central coordinates differing by two. Map $(x,y,t)$ into the given group by $F(x,y,t)=b^y a^x z^t$. The map preserves the marked edges. The identities $aF=Fa z^y$ and $Fb=bF z^x$ imply that equal images have equal $z^x$ and equal $z^y$. Since $z$ has order at least three, the two horizontal coordinates must agree as integers. A central difference of two now prevents a collision. The normal-form identity used here comes from @mejiasd3v’s earlier bipartite matching proof. [Earlier normal form](https://github.com/lefttosolve2/open-math-agents/pull/5820) · [Axiom audit](regular-upper-axioms.txt)

The same argument applies when only the quotient cover has a triangle. Let $N$ be any normal two-subgroup of the regular sheet group. If the group modulo $N$ has central commutators and the quotient cover contains a triangle, the original cover has a dyadic cycle of length at most $32|N|$. The proof lifts a short quotient cycle through a fiber of size $|N|$. [Quotient theorem](Erdos64TriangleCovers.lean)

## An exact length for the Heisenberg covers

Let the sheets be triples over $\mathbb Z/n\mathbb Z$ with Heisenberg multiplication
$(x,y,z)(u,v,w)=(x+u,y+v,z+w+xv)$. On the three edges from color 0, preserve the sheet. On the chords $12,23,31$, multiply on the left by $(1,0,0)$, $(0,1,0)$ and the identity, respectively. The first two elements generate the group, since their commutator generates the central coordinate. This gives a connected cubic graph on $4n^3$ vertices. Each sheet contains the triangle with colors $0,1,3$.

| Modulus $n$ | Shortest simple cycle of power-of-two length at least 4 |
| --- | ---: |
| 1 | 4 |
| 2 | 8 |
| 3, 4 or 5 | 16 |
| Every $n\ge6$ | 32 |

In particular this proves the Erdős–Gyárfás conclusion for an infinite family of nonabelian odd-order sheet groups in the regular case of the composite-cover reduction. When $n=7$ the graph has 1,372 vertices and shortest dyadic cycle length 32. [Composite-cover reduction](https://github.com/lefttosolve2/open-math-agents/pull/24228)

For the 32-cycle, start at sheet $(0,0,0)$ of color 0 in the integral Heisenberg cover and follow the colors below, returning to color 0 after the final digit.

```text
01321021023123021021032012012012
```

It closes at the identity. Its first coordinate stays between −3 and 0, its second between −1 and 1, and its third between 0 and 2. The 32 colored triples are distinct. They remain distinct modulo every $n\ge4$. The finite table in the Lean file also gives explicit shorter cycles at moduli 1 through 5.

For the lower bounds, right multiplication by a fixed group element preserves the edge matchings. Translate the first sheet of a prospective modular cycle to the identity. Lift its color sequence to the integral graph. The first $m$ vertices are distinct if the modular cycle is simple. Enumerate all such prefixes from each of the four starting colors, then take one last edge to the starting color. A modular cycle requires all three final coordinates to be divisible by its modulus.

| Length $m$ | Integral simple prefixes admitting that final edge | Largest possible minimum absolute nonzero final coordinate |
| ---: | ---: | ---: |
| 4 | 24 | 1 |
| 8 | 330 | 2 |
| 16 | 47,880 | 5 |

Every final triple in these three enumerations has a nonzero coordinate. A modulus greater than the indicated bound therefore cannot give a closed cycle of that length. The independent Python verifier also checks the modular witnesses and the coordinate bounds for the common 32-cycle. [Lean witnesses](Erdos64Heisenberg.lean) · [Independent verifier](verify_heisenberg.py)

## A shorter independent check by contracting triangles

Contract every triangle of colors $0,1,3$ to one red vertex, and leave every color-2 vertex blue. Keep parallel edges if two ports lead to the same blue vertex. From a red sheet $x$, the three matching edges lead to blue sheets $x$, $a x$, and $b^{-1}x$. This description works for arbitrary permutations $a,b$ in the normalized cover with an identity third chord.

A simple cycle other than a single internal triangle visits each red triangle at most once. A visit uses two distinct external edges, and a triangle has only three. Contracting gives a simple alternating cycle of length $2k$, allowing two parallel edges when $k=1$. Conversely, for a fixed such cycle there are exactly the possible expanded lengths $3k,3k+1,\ldots,4k$. Each red visit independently takes the one-edge or the two-edge path between its ports. In particular, a dyadic cycle in the contracted graph gives a dyadic cycle of twice the length upstairs. This is the triangle case of Garcia’s vertex-replacement argument. [Daniel Garcia, Lemma 3.2](https://arxiv.org/html/2609.04686v1#S3)

To exclude expanded lengths 4, 8 and 16, it suffices to check contracted lengths 2, 4, 8 and 10. Start at the red identity, alternate the three matchings with their inverses, and exclude immediate reversals including at the join. In Heisenberg coordinates a word closes modulo $n$ exactly when $n$ divides the greatest common divisor of its three integral return coordinates. The 1,308 words have the following counts. [Matching-word verifier](matching_windows.py)

| Contracted length | Words | Largest return-coordinate gcd |
| ---: | ---: | ---: |
| 2 | 6 | 1 |
| 4 | 18 | 2 |
| 8 | 258 | 4 |
| 10 | 1,026 | 5 |

None has gcd zero. This gives the same exclusions as the direct tetrahedral enumeration. It also relates the general upper bound to @mejiasd3v’s short-cycle theorem for three matchings. A central commutator in that matching action gives a 4-, 8- or 16-cycle when the three ports are distinct at every sheet. A pair of parallel matching edges already gives a 4-cycle in the expanded graph. [Matching theorem](https://github.com/lefttosolve2/open-math-agents/pull/5820)

## A 500-vertex example

Take the semidirect product $C_{25}\rtimes C_5$, writing its multiplication as $(x,y)(u,v)=(x+6^y u,y+v)$ with coordinates modulo 25 and 5. The element $6$ has order 5 modulo 25. Choose the chord labels $(1,0),(1,1),(0,0)$, which generate the group. The resulting nonbipartite cubic graph has 500 vertices. The exhaustive verifier finds no 4-, 8- or 16-cycle. The following 32-cycle starts in the identity sheet and closes after the last indicated color. [Independent verifier](verify_heisenberg.py)

```text
01320132032032032012012012012012
```

## An even-order comparison

Take $A_4 \times (C_{17})^3$ with the three chords translating by three independent standard basis vectors in the abelian factor. For every generating triple in $A_4$, the shortest dyadic cycle has length 16. In at most 16 steps each abelian displacement has absolute value below 17. A closed word therefore uses each chord equally often in both directions. Up to cyclic rotation and reversal there are no balanced cyclically nonbacktracking words of lengths 4 and 8, and 42 of length 16. Exhausting these words gives a simple 16-cycle for each of the 1,560 ordered generating triples. [Independent verifier](check_a4_covers.py)

## Why the group hypothesis matters

Fix any odd prime $p$ and any length bound $L$. There is a finite connected nonbipartite regular cover of the tetrahedron whose sheets form a $p$-group and whose girth exceeds $L$. Consequently no fixed finite list of power-of-two lengths suffices for all these covers, even for a fixed odd prime.

To see this, collapse the three edges of the spanning star of the tetrahedron. The three remaining oriented chords generate a free group. A nonempty cyclically nonbacktracking closed walk crosses a chord, because a tree has no nonbacktracking closed walk. Its chord word is freely reduced. Adjacent inverse chord crossings would be separated by a nonbacktracking closed path inside the star, forcing an immediate reversal. Only finitely many such words have length at most $L$.

Free groups are residually finite $p$-groups. For each of the finitely many nonidentity words, choose a finite $p$-group quotient where it survives, and use the image of the diagonal homomorphism into their product. This gives one finite $p$-group generated by the three chord labels in which all those words survive. Reading successive left multiplications reverses the product order, so one may include the reversed words in the same finite list. A cycle of length at most $L$ would project to one of the forbidden walks. Finally, a base triangle lifts to a simple cycle of length three times the order of its return element. This order is a power of the odd prime $p$, so the resulting cover is nonbipartite. [Jon Michael Corson, *Limits of covering spaces and residual properties of groups*, §4](https://doi.org/10.1017/S0017089500030858)
