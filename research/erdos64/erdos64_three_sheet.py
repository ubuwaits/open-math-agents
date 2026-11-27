"""Verify that every three-sheeted cover of the 28-vertex example has a C16.

Run with Python 3. Every permutation of three sheets is uniquely x ↦ sx+b
on F_3, with sign s in {1,-1}. Relabel the sheets along a spanning tree
so that its edge maps are the identity. The 15 other edges retain arbitrary
permutations; traversing an edge backward applies the inverse permutation.

If none of the base 16-cycles lifts to a 16-cycle, each return permutation
is fixed-point-free, hence has positive sign and a nonzero translation.
The sign constraints leave only two assignments. In each one a small
collection of translation forms cannot all be nonzero. A fixed sheet gives
a simple lifted 16-cycle because its projection already visits 16 different
vertices. This script checks the finite certificate independently of Lean.
"""

from collections import deque
from itertools import product


def base_graph():
    # Vertex 7*i+x lies in color i on sheet x. Chord voltages on 12,23,31
    # are 0,1,2, as in Erdos64Tetrahedron.sevenCover.
    voltage = ((0, 0, 0, 0), (0, 0, 0, -2), (0, 0, 0, 1), (0, 2, -1, 0))
    return [
        [7 * j + (x + voltage[i][j]) % 7 for j in range(4) if i != j]
        for i in range(4) for x in range(7)
    ]


def cotree_edges(graph):
    seen = {0}
    queue = deque([0])
    tree = set()
    while queue:
        u = queue.popleft()
        for v in graph[u]:
            if v not in seen:
                seen.add(v)
                tree.add(tuple(sorted((u, v))))
                queue.append(v)
    assert len(seen) == 28 and len(tree) == 27
    edges = [(u, v) for u, neighbors in enumerate(graph) for v in neighbors
             if u < v and (u, v) not in tree]
    assert len(edges) == 15
    return {edge: index for index, edge in enumerate(edges)}


def sixteen_cycles(graph):
    # Starting at the smallest vertex and choosing one orientation counts
    # each unoriented simple cycle once.
    def extend(path):
        if len(path) == 16:
            if path[0] in graph[path[-1]] and path[1] < path[-1]:
                yield tuple(path)
            return
        for v in graph[path[-1]]:
            if v > path[0] and v not in path:
                yield from extend(path + [v])

    for root in range(len(graph)):
        yield from extend([root])


def cotree_word(cycle, edges):
    word = []
    for u, v in zip(cycle, cycle[1:] + cycle[:1]):
        edge = tuple(sorted((u, v)))
        if edge in edges:
            word.append((edges[edge], u < v))
    return word


def translation_form(word, signs, dimension):
    # After each step the current sheet is ±x plus a linear combination
    # of the unknown chord translations. Only the coefficients are needed.
    row = [0] * dimension
    for edge, forward in word:
        sign = -1 if signs & (1 << edge) else 1
        row = [(sign * value) % 3 for value in row]
        row[edge] = (row[edge] + (1 if forward else -sign)) % 3
    return row


def coordinates(rows):
    # Echelon basis over F_3. Values of the basis forms at any assignment
    # determine all the forms, so a rank-r test takes only 3^r cases.
    basis = {}
    for original in rows:
        row = original.copy()
        for pivot, vector in sorted(basis.items()):
            coeff = row[pivot]
            row = [(a - coeff * b) % 3 for a, b in zip(row, vector)]
        if any(row):
            pivot = next(i for i, value in enumerate(row) if value)
            scale = pow(row[pivot], -1, 3)
            basis[pivot] = [scale * value % 3 for value in row]
    vectors = sorted(basis.items())
    result = []
    for original in rows:
        row = original.copy()
        coeffs = []
        for pivot, vector in vectors:
            coeffs.append(row[pivot])
            row = [(a - coeffs[-1] * b) % 3 for a, b in zip(row, vector)]
        assert not any(row)
        assert all(sum(c * v[i] for c, (_, v) in zip(coeffs, vectors)) % 3 == value
                   for i, value in enumerate(original))
        result.append(coeffs)
    return result


def main():
    graph = base_graph()
    edges = cotree_edges(graph)
    words = [cotree_word(cycle, edges) for cycle in sixteen_cycles(graph)]
    assert len(words) == 441
    supports = set()
    for word in words:
        parity = 0
        for edge, _ in word:
            parity ^= 1 << edge
        supports.add(parity)
    signs = [
        mask for mask in range(1 << len(edges))
        if all(bin(support & mask).count("1") % 2 == 0 for support in supports)
    ]
    assert signs == [0, (1 << 15) - 1]
    certificates = ([43, 189, 89, 58, 225, 111, 326], [36, 212, 89, 76, 340, 46])
    for mask, indices, expected_rank in zip(signs, certificates, [4, 3]):
        forms = [translation_form(words[i], mask, len(edges)) for i in indices]
        forms = coordinates(forms)
        assert len(forms[0]) == expected_rank
        for values in product(range(3), repeat=expected_rank):
            assert any(sum(a * b for a, b in zip(form, values)) % 3 == 0 for form in forms)
        print(f"Sign mask {mask}: {len(forms)} cycles, rank {expected_rank}, "
              f"all {3 ** expected_rank} evaluations checked.")
    print("Every three-sheeted cover has a simple lift of a base 16-cycle.")


if __name__ == "__main__":
    main()
