"""Check the 38-vertex cyclic Haar graph with shifts 0, 1, 8."""
from collections import Counter

P = 19
SHIFTS = (0, 1, 8)
RING = (0, 19, 11, 30, 3, 22, 2, 21, 1, 28, 8, 35, 15, 34, 7, 27)


def graph():
    adjacency = [set() for _ in range(2 * P)]
    for left in range(P):
        for shift in SHIFTS:
            right = P + (left + shift) % P
            adjacency[left].add(right)
            adjacency[right].add(left)
    return adjacency


def enumerate_cycles(adjacency):
    # The smallest vertex fixes the starting point. Order its two incident
    # cycle edges to retain exactly one of the two traversal directions.
    counts = Counter()
    lengths = {4, 8, 16}
    def visit(start, path, seen):
        last = path[-1]
        if len(path) in lengths and start in adjacency[last] and path[1] < last:
            counts[len(path)] += 1
        if len(path) == max(lengths):
            return
        for vertex in adjacency[last]:
            if vertex > start and vertex not in seen:
                visit(start, path + [vertex], seen | {vertex})
    for start in range(len(adjacency)):
        visit(start, [start], {start})
    return {length: counts[length] for length in sorted(lengths)}


if __name__ == "__main__":
    adjacency = graph()
    assert all(len(neighbors) == 3 for neighbors in adjacency)
    assert len(set(RING)) == len(RING) == 16
    assert all(RING[(i + 1) % 16] in adjacency[x] for i, x in enumerate(RING))
    def shift(x):
        return (x // P) * P + (x + 1) % P
    def swap(x):
        return (1 - x // P) * P + (-x) % P
    for permutation in (shift, swap):
        assert len({permutation(x) for x in range(2 * P)}) == 2 * P
        assert all({permutation(y) for y in adjacency[x]} == adjacency[permutation(x)]
                   for x in range(2 * P))
    reached = {0}
    while (more := reached | {shift(x) for x in reached} | {swap(x) for x in reached}) != reached:
        reached = more
    assert len(reached) == 2 * P
    counts = enumerate_cycles(adjacency)
    assert counts == {4: 0, 8: 0, 16: 1995}
    print("38 vertices, cubic and vertex-transitive, shifts (0, 1, 8)")
    print("Number of undirected simple cycles by length:", counts)
    print("One 16-cycle:", RING)
