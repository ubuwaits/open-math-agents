# Partial results on Erdős problem 64

Chad Mazzola ([@ubuwaits](https://github.com/ubuwaits)), using Codex.

The Erdős–Gyárfás conjecture asks whether every finite simple graph with minimum degree at least three has a simple cycle whose length is a power of two. The general conjecture remains open. [Problem statement](https://lefttosolve.com/p/Erdos64.erdos_64)

## Results

1. **Signed affine covers of the tetrahedron.** Replace each vertex of the complete graph on four vertices by a set of sheets indexed by an abelian group. Along each of the six edges, match sheets by an independently chosen map of the form `x ↦ x+a` or `x ↦ −x+a`. The resulting graph contains a simple cycle of length 4, 8, or 16. This also holds for infinite sheet groups. The bound 16 is attained on 28 vertices by a seven-sheet cyclic cover with shifts 0, 1, and 2 on the chords 12, 23, and 31, respectively. [Signed affine theorem](Erdos64AffineCovers.lean) · [Translation theorem and sharp example](Erdos64Tetrahedron.lean)
2. **Finite covers of an arbitrary graph.** For a given simple cycle of length `n`, an orbit of length `d` in its return permutation gives a simple cycle of length `n*d` upstairs. Having 1, 2, or 4 sheets guarantees that every possible return permutation has a power-of-two orbit. A finite two-group acting by edge translations also preserves the existence of a power-of-two lift. When the sheets are an abelian group of order $2^r$, arbitrary affine edge matchings also preserve every dyadic base cycle. A cycle of length $2^k$ lifts to one of length between $2^k$ and $2^{k+r}$. Among finite abelian groups, the powers of two are exactly the orders for which every affine permutation has a power-of-two orbit. [Cycle lifting proofs](Erdos64CycleCovers.lean)
3. **Three-sheeted covers of the sharp example.** In every three-sheeted cover of the 28-vertex graph, at least one of its 441 simple 16-cycles lifts to a simple 16-cycle. After choosing a spanning tree, two sign assignments survive. For those assignments, 81 and 27 evaluations of small systems of linear forms suffice. A separate exhaustive implementation checks all remaining assignments. [Small certificate](erdos64_three_sheet.py) · [Exhaustive verification](exhaustive_three_sheet.py)
4. **Bipartite double covers.** Suppose a simple graph has no 4-cycle. Its bipartite double cover has an 8-cycle exactly when the original graph contains an 8-cycle, three internally disjoint paths of lengths 1, 2, and 4 between one pair of vertices, two disjoint triangles joined by an edge, or a triangle and pentagon sharing only one vertex. The last possibility requires degree at least four. For any cycle of length $n$ in the double cover, its projection either contains a simple $n$-cycle or contains a simple odd cycle of length at most $n/2$. For dyadic $n$ this odd length is strictly below $n/2$. [Double-cover proofs](Erdos64DoubleCover.lean)
5. **Limits of descent.** For each power of two $n\ge 8$ and each bound $R$, there is a finite connected bridgeless cubic graph whose bipartite double has an $n$-cycle, whose odd girth is $n/2-1$, and which has no power-of-two cycle of length at most $R$. A concrete example has 7,920 vertices, contains a triangle and a 64-cycle, and has no 4-, 8-, or 16-cycle. The verifier also checks an explicit octagon in the double of Exoo’s 78-vertex graph using Garcia’s published data. [Construction and proof](double-cover-construction.md) · [Computational check](verify_double_cover_example.py)
6. **Affine covers over vector spaces.** If the six matchings of the tetrahedron have the form $x\mapsto u x+a$ on a vector space over a division ring, for arbitrary nonzero scalars $u$, the graph contains a 4-, 8-, or 16-cycle. The same bound holds on a finite abelian group acted on by a group of automorphisms in which only the identity fixes a nonzero point. The seven-sheet example in item 1 attains the bound. [Lean proofs](Erdos64AffineCovers.lean)

## Official submission

The combined reduction applies these results to connected nonbipartite bridgeless cubic graphs. A locally bijective four-coloring identifies such a graph as a tetrahedral cover. All three of its matching permutations admit translation coordinates on an orbit when they commute. The signed affine, general affine, solvable prime-degree, and solvable power-of-two proofs then eliminate the corresponding cases. Chad Mazzola (@ubuwaits) submitted the single Lean file. The parent cubic reduction is due to @mejiasd3v, building on @JamesSlash’s bridge reduction. [Upstream pull request](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7329) · [Signed combined proof](https://github.com/ubuwaits/open-math-agents/commit/4f56b3f7aa32d607577e0de95663648a953b5e4a) · [Parent reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5246) · [Bridge reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/592)

The three remaining hypotheses cover graphs without a locally bijective four-coloring, composite-degree covers outside the affine and solvable power-of-two cases, and prime-degree covers with nonsolvable monodromy. On November 27, 2026, the upstream Lean kernel accepted the combined reduction with zero errors. It reported only `propext`, `Classical.choice`, and `Quot.sound`. [Combined proof](reductions/Erdos64.erdos_64.R1.H1.R1.H1.R1.H1.R1.lean) · [Upstream checker run](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/46048955140) · [Official verdict](reductions/upstream-verdict.json) · [Local checker verdict](reductions/combined-verdict.json)

The earlier signed two-stage derivation remains reproducible. Its first reduction isolated the unsigned and signed translation cases. Its second reduction supplied the general affine and solvable-group arguments. Both stages are incorporated in the combined submission. [Earlier signed first reduction](https://github.com/ubuwaits/open-math-agents/commit/035cf1264c5438e987b7033a58c519eece2f47aa) · [First upstream kernel verdict](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/46029671471) · [Second-stage Lean file](reductions/Erdos64.erdos_64.R1.H1.R1.H1.R1.H1.R1.H2.R1.lean) · [Second-stage local verdict](reductions/local-prime-reduction-verdict.json)

## Why arbitrary scalars work

Transport the sheet coordinates along the three edges from color 0 so that those matchings preserve the sheet. Write $p,q,r$ for the linear parts of the other three matchings, oriented along $12,23,31$. Traversing a Hamiltonian cycle of the tetrahedron composes two consecutive chords. The three possible linear parts are $qp,rq,pr$. If one of these, say $g$, is different from 1, a fixed point of its affine return map gives a 4-cycle. The fixed-point equation is $(1-g)x=b$, which has a solution over a division ring. In the finite-group version, subtraction of the image under $g$ has zero kernel by hypothesis and is therefore bijective.

If all three products equal 1, the group laws give $p=q=r$ and $p^2=1$. When $p=1$, all chords are translations. Otherwise $x+p(x)$ is fixed by $p$ for every $x$, so $p(x)=-x$. The signed theorem now applies. Lean checks the coordinate change for all six matchings, the general invertibility criterion, the finite fixed-point-free case, and the vector-space case. [Affine proofs](Erdos64AffineCovers.lean)

For example, on five sheets let the chords act by $x\mapsto 2x$, $x\mapsto x+1$, and the identity over the field of five elements. Translation by 1 is transitive, and multiplication by 2 has order 4. Every signed translation on a group of order five has order 1, 2, or 5, so the earlier signed-coordinate hypothesis cannot hold on any orbit. The new result gives a 4-cycle in this graph.

**Corollary for prime-degree covers.** Suppose the tetrahedral cover is connected, has a prime number $p$ of sheets, and the group generated by its three chord permutations is solvable. It then has a 4-, 8-, or 16-cycle. Indeed, connectedness makes the action transitive. A minimal nontrivial normal subgroup $N$ of this finite solvable permutation group is abelian, since its commutator subgroup is characteristic in $N$ and is proper by solvability. Its orbits have equal sizes dividing $p$. Since the action is faithful and $N$ is nontrivial, it is transitive. An element of the transitive abelian group $N$ fixing one point fixes all points, hence is the identity. Thus $N$ acts regularly and has order $p$. In coordinates given by $N$, every permutation normalizing $N$ is a translation followed by an automorphism of its cyclic group. These are exactly the scalar affine maps over the prime field, so the vector-space theorem applies. Lean checks both the transitive group-action theorem and the deduction from connectedness of the four-fiber graph. [Prime-sheet proof](Erdos64AffineCovers.lean)

## Why affine matchings preserve dyadic cycles on abelian two-groups

Let $f$ be the affine permutation obtained after one lap around a base cycle. Write the period of the zero sheet as $2^j m$, with $m$ odd. The orbit of zero under $g=f^{2^j}$ closes after $m$ steps. Add the $m$ sheets in that orbit and divide by $m$, which is possible uniquely in a finite abelian group of power-of-two order. The affine map $g$ fixes this average because it permutes the summands. Its sheet therefore has power-of-two period under $f$. In the other direction, if every affine permutation has such an orbit, apply the property to each translation. Every group element must have power-of-two order. [Cycle lifting and the converse](Erdos64CycleCovers.lean)

## Solvable covers with a power of two sheets

Suppose a finite connected graph cover has $2^r$ sheets and solvable monodromy. Every simple base cycle of length $2^k$ has a simple lift of length $2^d$ with $k\le d\le k+r$. In particular, a square in the tetrahedron gives a power-of-two cycle in every such cover. The upper bound for a general base cycle is sharp. The cyclic cover $C_{2^{k+r}}\to C_{2^k}$ that reduces the vertex index modulo $2^k$ has exactly one simple cycle up to orientation and starting point, of length $2^{k+r}$.

Let $g$ be the permutation of the sheets after one lap. For a finite solvable group acting transitively on a set $X$, an element of order coprime to $|X|$ fixes a point. To see this from Hall’s theorem, take the primes dividing the element’s order. The stabilizer of a point has index $|X|$, so its Hall subgroup for these primes is also a Hall subgroup of the full group. The cyclic group generated by the element lies in a conjugate of that Hall subgroup and hence fixes a point. Write the order of $g$ as $2^j m$ with $m$ odd. The preceding result gives a sheet fixed by $g^{2^j}$. Its period under $g$ is a power of two and is at most the sheet count. Lifting the base cycle from that sheet proves the bound. [P. Hall, *A Note on Soluble Groups* (1928)](https://doi.org/10.1112/jlms/s1-3.2.98)

The Lean proof derives the fixed-point lemma directly. In a faithful primitive solvable action, a nontrivial abelian normal subgroup acts regularly, so averaging a coprime-length orbit gives a fixed point. For an imprimitive action, apply induction first to the set of blocks and then inside a stabilized block. [Fixed-point and lifting proofs](Erdos64CycleCovers.lean) · [Application to the tetrahedron](reductions/Erdos64.erdos_64.R1.H1.R1.H1.R1.H1.R1.H2.R1.lean)

## Reproducing the checks

The four standalone Lean files use Lean 4.33.1. The project check used formal-conjectures revision `9097e2f90e66d2f6244209cb1c07f7120d17ec53` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The headline theorems report only `propext`, `Classical.choice`, and `Quot.sound`. [Local project verdict](local-reduction-verdict.json) · [Earlier upstream acceptance](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/46015736530)

To reproduce the combined submission in a separate prepared checkout, copy the [combined Lean file](reductions/Erdos64.erdos_64.R1.H1.R1.H1.R1.H1.R1.lean) to `reductions/Erdos64.erdos_64.R1.H1.R1.H1.R1.H1.R1.lean` there and run `tools/oma.sh check Erdos64.erdos_64.R1.H1.R1.H1.R1.H1.R1`.

The research branch root retains the first-stage reduction for comparison. From its root, with the pinned project environment installed by `tools/oma.sh setup`, run

```sh
tools/oma.sh check Erdos64.erdos_64.R1.H1.R1.H1.R1.H1.R1
proofs_dir="$PWD/research/erdos64"
(
  cd .oma/formal-conjectures || exit 1
  for proof in "$proofs_dir"/*.lean; do
    lake env lean "$proof" || exit 1
  done
)
```

The Python programs use the standard library. From this directory, run

```sh
python3 erdos64_three_sheet.py
python3 exhaustive_three_sheet.py
python3 search_cyclic_example.py
python3 enumerate_double_cover_images.py
python3 verify_double_cover_example.py
for mask in 0 1 2 3 4 5 6 7; do
  python3 search_affine_templates.py "$mask" || exit 1
done
```

The sign-mask search recovers the color words and the integer relations for every case. Mask 0 has 26 cases, mask 7 has 38, and each of the six mixed masks has two. The Lean proofs independently check every word and every implication between relations. [Search certificates](affine-certificates.json)
