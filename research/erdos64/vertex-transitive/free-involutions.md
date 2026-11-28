# Fixed-point-free involutions in a smallest counterexample

A smallest counterexample to Erdős–Gyárfás must have both kinds of vertex pair under every fixed-point-free involutory automorphism. At least one vertex is adjacent to its mate, and at least one vertex is nonadjacent to its mate. This restriction applies to graphs with any number of vertex orbits. [Lean theorem](Erdos64FreeInvolutions.lean) · [Axiom audit](free-axioms.txt)

Let t be the involution and collapse each pair {v,tv} to one vertex. A square-free graph cannot have two distinct neighbors of v in the same pair. If v is adjacent to w and tw, then v,w,tv,tw is a square. Every surviving quotient edge therefore lifts uniquely from either vertex of its starting pair. A quotient cycle of length n lifts to length n or 2n. [Cycle-lifting argument](Erdos64SymmetricCycles.lean)

The quotient vertex of v has degree d(v) when v and tv are nonadjacent, and degree d(v)−1 when they are adjacent. The quotient vertices that lose a degree form an independent set. An edge between two such pairs would lift to an edge v,w, completing the square v,w,tw,tv.

If all pairs are nonadjacent, the smaller quotient still has minimum degree at least three. Minimality gives a power-of-two cycle there, which lifts to another power-of-two cycle. If all pairs are adjacent, the independent set fills the quotient, contradicting the positive degrees. Thus any fixed-point-free involution on a minimum-order counterexample has a mixture of the two kinds of pair.

This is a separate checked consequence of the binary lifting argument in the signed root-level submission. [Root reduction](https://github.com/lefttosolve2/open-math-agents/pull/28718)
