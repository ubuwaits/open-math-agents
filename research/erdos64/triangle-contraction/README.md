# Triangle contraction in the Erdős–Gyárfás conjecture

Chad Mazzola (GitHub `@ubuwaits`), using Codex. [Signed submission](https://github.com/ubuwaits/open-math-agents/commit/9ab26f2e5da0345b99ba53115aece97e2e259f71) · [Upstream pull request #27543](https://github.com/lefttosolve2/open-math-agents/pull/27543) · [Upstream Lean check](https://github.com/lefttosolve2/open-math-agents/actions/runs/46138827889)

The Erdős–Gyárfás conjecture asks whether every finite simple graph of minimum degree at least three has a simple cycle of length a power of two. This contribution reduces the connected, bridgeless cubic branch to two smaller questions. A cubic graph has degree three at every vertex. A bridge is an edge whose removal disconnects its endpoints. [Original problem](https://lefttosolve.com/p/Erdos64.erdos_64) · [Parent reduction by @JamesSlash](https://github.com/lefttosolve2/open-math-agents/pull/592)

## The two questions

1. Does every connected bridgeless cubic graph with no triangle, square, or octagon have a power-of-two cycle?
2. In a connected bridgeless cubic graph, suppose at least one power-of-two cycle exists and every such cycle passes through a vertex r. Suppose also that r lies on no triangle. Is there a simple cycle through r whose length is one or two less than a power of two?

A positive answer to both questions implies the original bridgeless cubic statement. Both questions remain open in general. [Exact hypotheses and reduction](reductions/Erdos64.erdos_64.R1.H1.R1.H1.R2.lean)

## Why contraction works

Consider a hypothetical smallest counterexample to the bridgeless cubic statement. If it contains a triangle, each of its three vertices has one edge leaving the triangle. Two of those edges meeting the same outside vertex would form a square using the third triangle vertex. The outside endpoints are therefore distinct. Shrinking the triangle to a vertex r produces a smaller simple cubic graph. It stays connected. Each surviving edge has a unique lift, so an alternative path around that lift projects to an alternative walk around the surviving edge. Thus the quotient remains bridgeless. [Contraction proof](Erdos64CubicTriangle.lean)

Minimality gives a power-of-two cycle in the quotient. A cycle avoiding r keeps its length upstairs. A cycle of length n through r has two lifts. It can use the edge between its entry and exit ports, or it can visit the third triangle vertex on the way. Their lengths are n+1 and n+2. In particular, a triangle through r gives a square upstairs. The rooted question asks exactly for a quotient cycle whose extra one or two edges solve the problem upstairs.

For a collection of disjoint triangular replacements, a cycle of length n that visits s replaced vertices has a simple lift of each length from n+s to n+2s inclusive. Any t of its s triangle detours can use the third vertex. The projection keeps the chosen paths at distinct base vertices disjoint. This is the triangle case of Daniel Garcia’s window lemma. [Lean proof](Erdos64TriangleExpansion.lean) · [Garcia, Lemma 3.2](https://arxiv.org/html/2609.04686v1#S3)

If at least half of a base cycle’s vertices were replaced, one lift has exactly twice its length. In particular, if the replacement vertices meet every base edge, *every* base cycle doubles. The successor of each unreplaced vertex on the cycle is replaced, giving an injection from unreplaced vertices to replaced ones. This also covers replacing a whole shore of a cubic bipartite graph.

## Verification

The upstream run accepted the guarded statement of the reduction at the project’s pinned formal-conjectures commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. The independent audit checks the interval lemma, both doubling consequences, the two single-vertex lifts, the outgoing edges, preservation of bridgelessness, the full contraction, and the final reduction. All eight depend only on `propext`, `Classical.choice`, and `Quot.sound`. [Upstream verdict](upstream-verdict.json) · [Local verdict](local-verdict.json) · [Axiom audit](axioms.txt)

To reproduce, use a disposable project checkout with the pinned Lean environment and the parent reduction available. Set `proofs_dir` to the absolute path of this research directory. From that checkout run the following commands.

```sh
cp "$proofs_dir"/reductions/Erdos64.erdos_64.R1.H1.R1.H1.R2.lean reductions/ &&
tools/oma.sh check Erdos64.erdos_64.R1.H1.R1.H1.R2 &&
(
  cd .oma/formal-conjectures || exit 1
  lake build OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R2 || exit 1
  for name in Erdos64TriangleExpansion Erdos64CubicTriangle; do
    cp "$proofs_dir/$name.lean" . || exit 1
    lake env lean -o ".lake/build/lib/lean/$name.olean" "$name.lean" || exit 1
  done
  lake env lean "$proofs_dir/TriangleContractionAudit.lean"
)
```
