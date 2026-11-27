"""Check an explicit cubic graph whose bipartite double has a short cycle."""

from collections import deque


MODULUS = 11
IDENTITY = (1, 0, 0, 1)
GENERATORS = ((1, 2, 0, 1), (1, 9, 0, 1), (1, 0, 2, 1), (1, 0, 9, 1))
CORE_EDGES = ((0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 1))


def multiply(left, right):
    a, b, c, d = left
    e, f, g, h = right
    return tuple(value % MODULUS for value in
                 (a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h))


def cayley_graph():
    elements = [IDENTITY]
    index = {IDENTITY: 0}
    neighbors = []
    for element in elements:
        row = []
        for generator in GENERATORS:
            product = multiply(element, generator)
            if product not in index:
                index[product] = len(elements)
                elements.append(product)
            row.append(index[product])
        neighbors.append(row)
    return neighbors


def first_relation(neighbors, limit):
    # Read all positive-length freely reduced words, in increasing length.
    frontier = [(0, None)]
    for length in range(1, limit + 1):
        frontier = [(neighbor, step) for vertex, previous in frontier
                    for step, neighbor in enumerate(neighbors[vertex])
                    if previous is None or step != (previous ^ 1)]
        if any(vertex == 0 for vertex, _ in frontier):
            return length
    return None


def replacement(base):
    neighbors = [set() for _ in range(6 * len(base))]
    for block, row in enumerate(base):
        for u, v in CORE_EDGES:
            left, right = 6 * block + u, 6 * block + v
            neighbors[left].add(right)
            neighbors[right].add(left)
        for step, other in enumerate(row):
            neighbors[6 * block + 2 + step].add(6 * other + 2 + (step ^ 1))
    return neighbors


def connected(neighbors):
    seen = {0}
    queue = deque([0])
    while queue:
        for neighbor in neighbors[queue.popleft()]:
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append(neighbor)
    return len(seen) == len(neighbors)


def check_cycle(neighbors, cycle):
    assert len(cycle) >= 3 and len(set(cycle)) == len(cycle)
    assert all(v in neighbors[u] for u, v in zip(cycle, cycle[1:] + cycle[:1]))


def check_excluded_cycles(neighbors, lengths):
    # Left multiplication in the matrix group preserves all port labels.
    # Every vertex is therefore equivalent to one of these six roots.
    limit = max(lengths)
    for root in range(6):
        used = {root}

        def visit(vertex):
            if len(used) in lengths:
                assert root not in neighbors[vertex], (root, len(used))
            if len(used) == limit:
                return
            for neighbor in neighbors[vertex]:
                if neighbor not in used:
                    used.add(neighbor)
                    visit(neighbor)
                    used.remove(neighbor)

        visit(root)


def check_long_cycle(base, graph):
    # A has order 11. Use two four-edge and nine five-edge internal paths.
    cycle = []
    block = 0
    for position in range(11):
        route = [3, 4, 5, 1, 2] if position < 2 else [3, 4, 5, 1, 0, 2]
        cycle.extend(6 * block + port for port in route)
        block = base[block][0]
    assert block == 0 and len(cycle) == 64
    check_cycle(graph, cycle)


def check_double_octagon(graph):
    word = [0, 1, 2, 0, 1, 5, 4, 3]
    lifted = [(v, position % 2) for position, v in enumerate(word)]
    assert len(set(lifted)) == 8
    for (u, i), (v, j) in zip(lifted, lifted[1:] + lifted[:1]):
        assert v in graph[u] and i != j


def main():
    base = cayley_graph()
    assert len(base) == 1320 and first_relation(base, 9) == 9
    graph = replacement(base)
    assert len(graph) == 7920 and connected(graph)
    for vertex, row in enumerate(graph):
        assert len(row) == 3 and vertex not in row
        assert all(vertex in graph[neighbor] for neighbor in row)
    check_cycle(graph, [0, 1, 2])
    check_excluded_cycles(graph, {4, 8, 16})
    check_long_cycle(base, graph)
    check_double_octagon(graph)
    print("Base: 1,320 vertices, girth 9. Replacement: 7,920 vertices, cubic.")
    print("Downstairs: triangle and 64-cycle, no 4-, 8-, or 16-cycle.")
    print("Upstairs: simple 8-cycle.")


if __name__ == "__main__":
    main()
