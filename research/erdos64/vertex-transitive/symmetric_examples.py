"""Verify the orders and shortest dyadic cycles of two symmetric cubic graphs."""

from itertools import product


def cycles(graph, length):
    """Enumerate unoriented simple cycles using their least vertex as the first."""
    def extend(start, path, used):
        if len(path) == length:
            if start in graph[path[-1]] and path[1] < path[-1]:
                yield tuple(path)
            return
        for neighbor in graph[path[-1]]:
            if neighbor > start and neighbor not in used:
                yield from extend(start, path + [neighbor], used | {neighbor})

    for start in graph:
        yield from extend(start, [start], {start})


def check_automorphisms(graph, generators):
    for permutation in generators:
        assert {permutation(v) for v in graph} == graph.keys()
        for v, neighbors in graph.items():
            assert {permutation(w) for w in neighbors} == graph[permutation(v)]
    orbit = {min(graph)}
    while True:
        new = orbit | {g(v) for v in orbit for g in generators}
        if new == orbit:
            break
        orbit = new
    assert orbit == graph.keys()


def verify(name, graph, generators, expected):
    assert all(len(neighbors) == 3 for neighbors in graph.values())
    assert all(v not in neighbors and all(v in graph[w] for w in neighbors)
               for v, neighbors in graph.items())
    check_automorphisms(graph, generators)
    counts = {length: sum(1 for _ in cycles(graph, length)) for length in expected}
    assert counts == expected
    shortest = next(length for length, count in counts.items() if count)
    assert 2 * shortest == len(graph)
    witness = next(cycles(graph, shortest))
    print(f"{name}: {len(graph)} vertices, cycle counts {counts}, witness {witness}")


def main():
    cube = {v: {v ^ bit for bit in (1, 2, 4)} for v in range(8)}
    verify("Cube", cube, [lambda v, bit=bit: v ^ bit for bit in (1, 2, 4)], {4: 6})

    # Generalized Petersen graph G(8,3), also known as the Möbius–Kantor graph.
    mk = {}
    for layer, i in product(range(2), range(8)):
        step = 1 if layer == 0 else 3
        mk[(layer, i)] = {(layer, (i - step) % 8), (layer, (i + step) % 8), (1 - layer, i)}
    rotate = lambda v: (v[0], (v[1] + 1) % 8)
    swap = lambda v: (1 - v[0], 3 * v[1] % 8)
    verify("Möbius–Kantor", mk, [rotate, swap], {4: 0, 8: 30})


if __name__ == "__main__":
    main()
