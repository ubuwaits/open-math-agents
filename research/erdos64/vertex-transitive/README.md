# Power-of-two cycles in vertex-transitive graphs of power-of-two order

Chad Mazzola (GitHub `@ubuwaits`), using Codex. [Signed proof](https://github.com/ubuwaits/open-math-agents/commit/2d21643a6441d14c9345185d3958b256e81e4fcc) · [Root reduction #28718](https://github.com/lefttosolve2/open-math-agents/pull/28718) · [Official checker run](https://github.com/lefttosolve2/open-math-agents/actions/runs/46142355729)

**Theorem.** Let G be a finite simple vertex-transitive graph of minimum degree at least three. If the number N of vertices is a power of two and N ≥ 8, then G contains a simple cycle of power-of-two length between 4 and N/2 inclusive. For N = 4, the graph is complete and contains a square. Vertex-transitive means that an automorphism can carry any vertex to any other. [Lean theorem and reduction](reductions/Erdos64.erdos_64.R4.lean)

**Rooted consequence.** Suppose G has more than four vertices and contains at least one power-of-two cycle. For each vertex r, some power-of-two cycle avoids r, regardless of the order of G. This excludes every vertex-transitive graph from the rooted obstruction in the triangle-contraction reduction. At order four, every vertex lies on a triangle. [Rooted triangle branch](https://github.com/lefttosolve2/open-math-agents/pull/27543) · [Axiom audit](axioms.txt)

## Proof

1. A Sylow 2-subgroup P of the transitive automorphism group is transitive on the vertices. For a vertex v, its orbit under P has size s. The index of the vertex stabilizer in the full group is N. Intersecting the stabilizer with P shows that N divides s times the odd index of P. Thus N divides s, which is at most N. In the faithful action of P, a central involution t has no fixed vertex. A single fixed vertex and transitivity would force it to fix every vertex. [Group arguments](Erdos64TwoGroups.lean)
2. Partition the vertices into pairs {v,tv}. If v is adjacent to tv, transitivity makes every vertex adjacent to its mate, and any neighbor w distinct from tv gives the square v,w,tw,tv. If v is adjacent to both w and tw, the square is v,w,tv,tw. In a square-free graph the quotient therefore has a unique neighboring lift of every incident edge. It has half as many vertices, the same local degrees, and a transitive quotient 2-group. [Quotient and induction](Erdos64VertexTransitive.lean)
3. Follow a simple quotient cycle of length n upstairs, tracking both the cycle position and the lifted vertex. The successor is a permutation on at most 2n states, because each neighboring lift is unique in both directions. Its orbit length is a positive multiple of n. The orbit therefore gives a simple cycle of length n or 2n. [Cycle-lifting proof](Erdos64SymmetricCycles.lean)
4. When the original graph has eight vertices, a square-free quotient construction would give a two-sheeted cover of K4. Fix a lift of one vertex and label the three leaves of its lifted star. Each of the three edges between the corresponding quotient leaves either joins the selected lifts or crosses to their mates. Two of these three choices agree. They meet at a common leaf, and the lifted star and those two edges form a square, using the mate of the common leaf when both choices cross. This proves the base case. Each subsequent descent halves the graph order and each lift increases a cycle length by at most twofold. [Four-vertex quotient argument](Erdos64BinaryQuotients.lean)

For the rooted consequence, if every cycle of a given length passes through r, every automorphic image of r lies on each such cycle. In a vertex-transitive graph such a cycle is Hamiltonian. Its dyadic length forces the graph order to be a power of two, and the theorem gives a shorter dyadic cycle when the order exceeds four.

## An obstruction without transitivity

In a smallest counterexample to the full conjecture, every fixed-point-free involutory automorphism must send some vertices to neighbors and others to nonneighbors. Its pairs that lose a degree form an independent set in the quotient. [Proof and exact degree formula](free-involutions.md)

## Two examples attaining the bound

The cube on eight vertices has six unoriented squares. The Möbius–Kantor graph on sixteen vertices, the generalized Petersen graph G(8,3), has no square and has thirty unoriented octagons. Their shortest power-of-two cycles have lengths four and eight respectively. The independent Python check constructs the graphs from their edges, verifies that explicit automorphisms act transitively, and enumerates the cycles. [Verifier](symmetric_examples.py) · [Verified counts and witnesses](examples.txt) · [SageMath graph definition](https://doc.sagemath.org/html/en/reference/graphs/sage/graphs/graph_generators.html#sage.graphs.graph_generators.GraphGenerators.MoebiusKantorGraph)

## What remains in the root reduction

1. Connected graphs with at least two vertex orbits, after imposing the degree-three conditions on edges and neighborhoods.
2. Connected vertex-transitive cubic graphs whose order has an odd prime factor.

Both branches exclude squares and octagons. The first degree reduction is due to @JamesSlash. Related results include Michael C. Burkhart’s proof for Cayley graphs of finite odd-order and nilpotent groups. Morris, Spiga and Verret study normal quotients of cubic vertex-transitive graphs. [Degree reduction #466](https://github.com/lefttosolve2/open-math-agents/pull/466) · [Burkhart](https://arxiv.org/abs/2611.05060) · [Morris, Spiga and Verret](https://doi.org/10.37236/4842)

## Reproducing the checks

The submission contains the complete proof. In a disposable project checkout with the pinned Lean environment installed, set `proofs_dir` to the absolute path of this research directory. The local and upstream checks independently audit the guarded root statement. [Local verdict](local-verdict.json) · [Upstream verdict](upstream-verdict.json)

```sh
cp "$proofs_dir/reductions/Erdos64.erdos_64.R4.lean" reductions/ &&
tools/oma.sh check Erdos64.erdos_64.R4 &&
(
  cd .oma/formal-conjectures || exit 1
  lake build OMAReductions.R_Erdos64_erdos_64_R4 || exit 1
  lake env lean "$proofs_dir/SymmetricAudit.lean"
)
python3 "$proofs_dir/symmetric_examples.py"
```

The shorter research modules use the triangle-cycle construction already archived with the preceding reduction. [Dependency](https://github.com/ubuwaits/open-math-agents/blob/a2cc1fb4972eefb77f20e184fc6aef546ba4f569/research/erdos64/triangle-contraction/Erdos64TriangleExpansion.lean)
