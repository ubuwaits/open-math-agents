# Power-of-two cycles at twice a prime order

Chad Mazzola (@ubuwaits), using Codex, 28 November 2026.

Every finite simple vertex-transitive graph of minimum degree at least three on $2p$ vertices, for a prime $p$, contains a simple cycle of length 4, 8, or 16. In fact a nontrivial action by automorphisms of a group of order $p$ on those $2p$ vertices suffices. A 38-vertex cubic graph shows that 16 is sharp. [Lean proof](Erdos64TwicePrime.lean) · [Kernel axiom audit](axioms.txt) · [Root submission](https://github.com/lefttosolve2/open-math-agents/pull/28718)

## The argument

A transitive permutation group on $2p$ points has order divisible by $p$, by orbit–stabilizer. Cauchy's theorem gives an automorphism of order $p$. Each moving orbit has exactly $p$ vertices, so there are one or two moving orbits. [Prime action and transitive corollary](Erdos64TwicePrime.lean)

With one moving orbit, identify its vertices with a cyclic group. If all three neighbors of a vertex lie inside that orbit, two different, nonopposite steps give a square. Otherwise a fixed neighbor is adjacent to the whole moving orbit. Two neighbors inside give a square through that fixed neighbor. Two neighbors outside are fixed and have every orbit vertex as a common neighbor. Three neighbors force one of these two possibilities.

With two moving orbits, identify the vertices with two copies of the same cyclic group. The following argument works for every abelian group. If the layers share an edge, translating it gives a matching. Number the layers so its edges are $L_x R_x$. With an internal step $s$ on the left and $t$ on the right, equal or opposite steps give a square. Otherwise the following eight vertices are distinct and form a cycle.

```text
L(0), L(s), R(s), R(s+t), L(s+t), L(t), R(t), R(0), back to L(0).
```

If one layer has no internal neighbor, minimum degree supplies three cross-neighbors. Their translates form an abelian Haar graph, which has a 4-, 8-, or 16-cycle by José Mejias's merged three-matching lemma. If there is no edge between the layers, three internal neighbors give a square. [Two-orbit proof](Erdos64TwoOrbits.lean) · [José Mejias's proof in PR 5246](https://github.com/lefttosolve2/open-math-agents/pull/5246)

## A sharp example

Take two copies of the integers modulo 19. Join each left $i$ to right $i$, $i+1$, and $i+8$. Translation by one and inversion together with a layer swap act transitively on all 38 vertices. Independent Python enumeration over the full graph counts each undirected simple cycle once. There are no 4- or 8-cycles and exactly 1,995 cycles of length 16. The program also checks an explicit 16-cycle and the stated automorphisms. [Enumeration](sharp_twice_prime.py) · [Results and witness](example.txt)

## Verification

The two Lean modules compiled with Lean 4.33.1 and the site's pinned formal-conjectures revision. All eight listed declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The source dependencies are the triangle-expansion module and the upstream reduction containing the abelian Haar lemma. [Audit declarations](TwicePrimeAudit.lean) · [Pinned triangle-expansion source](https://github.com/ubuwaits/open-math-agents/blob/a2cc1fb4972eefb77f20e184fc6aef546ba4f569/research/erdos64/triangle-contraction/Erdos64TriangleExpansion.lean) · [Pinned Haar source](https://github.com/lefttosolve2/open-math-agents/blob/d416120da3ed9e50ebe591da10f05afe07dd11d3/reductions/Erdos64.erdos_64.R1.H1.R1.H1.R1.lean) · [Formal-conjectures revision](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53)

Left to Solve's upstream checker accepted the strengthened root reduction at signed commit `ff36b7b18d9e`. The public desk records the result under @ubuwaits. [Upstream run](https://github.com/lefttosolve2/open-math-agents/actions/runs/46146378547) · [Upstream verdict](upstream-verdict.json) · [Public desk note](https://lefttosolve.com/api/desk/board?problem=Erdos64.erdos_64&since=137532)
