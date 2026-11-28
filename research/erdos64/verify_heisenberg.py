"""Independent standard-library verification of tetrahedral-cover cycle lengths."""

from collections import Counter
from itertools import combinations
from math import gcd


def heisenberg_step(vertex, color):
    old_color, x, y, z = vertex
    if (old_color, color) == (1, 2):
        return color, x + 1, y, z + y
    if (old_color, color) == (2, 1):
        return color, x - 1, y, z - y
    if (old_color, color) == (2, 3):
        return color, x, y + 1, z
    if (old_color, color) == (3, 2):
        return color, x, y - 1, z
    return color, x, y, z


def semidirect_step(vertex, color):
    """Left multiplication in C25 ⋊ C5, with the action of 1 given by 6."""
    old_color, x, y = vertex
    factors = {(1, 2): (1, 0), (2, 1): (-1, 0), (2, 3): (1, 1), (3, 2): (-21, -1)}
    a, b = factors.get((old_color, color), (0, 0))
    return color, (a + (1 + 5*b)*x) % 25, (b + y) % 5


def endpoints(step, identity, length):
    """List final sheets of integer- or group-simple prefixes returning to their first color."""
    for first in range(4):
        initial = (first, *identity)
        visited = {initial}

        def walk(vertex):
            if len(visited) == length:
                if vertex[0] != first:
                    yield step(vertex, first)[1:]
                return
            for color in range(4):
                if color == vertex[0]:
                    continue
                following = step(vertex, color)
                if following in visited:
                    continue
                visited.add(following)
                yield from walk(following)
                visited.remove(following)

        yield from walk(initial)


def trace(step, identity, word):
    colors = [int(digit) for digit in word]
    path = [(colors[0], *identity)]
    for color in colors[1:] + colors[:1]:
        if color == path[-1][0]:
            raise ValueError("A base edge joins distinct colors")
        path.append(step(path[-1], color))
    return path


def residue(vertex, modulus):
    return (vertex[0], *(x % modulus for x in vertex[1:]))


def main():
    # In each row the key is the smallest absolute value of a nonzero coordinate.
    # A zero return would prevent such a coordinate from being selected.
    expected = {
        4: {1: 24},
        8: {1: 265, 2: 65},
        16: {1: 29214, 2: 12234, 3: 5084, 4: 1252, 5: 96},
    }
    for length, counts in expected.items():
        actual = Counter(min((abs(x) for x in end if x != 0), default=0)
                         for end in endpoints(heisenberg_step, (0, 0, 0), length))
        assert actual == counts, (length, actual)
        print(f"Length {length}, all four starting colors: {dict(sorted(actual.items()))}")

    witnesses = {1: "0123", 2: "01320132", 3: "0120120123023023",
                 4: "0120123123023123", 5: "0120120120120312"}
    for n, word in witnesses.items():
        reduced = [residue(v, n) for v in trace(heisenberg_step, (0, 0, 0), word)]
        assert reduced[0] == reduced[-1] and len(set(reduced[:-1])) == len(word)

    word = "01321021023123021021032012012012"
    path = trace(heisenberg_step, (0, 0, 0), word)
    assert path[0] == path[-1] and len(set(path[:-1])) == 32
    for u, v in combinations(path[:-1], 2):
        if u[0] == v[0]:
            # Every modulus identifying this pair must divide this gcd.
            assert 1 <= gcd(*(x-y for x, y in zip(u[1:], v[1:]))) <= 3
    print("Heisenberg covers: shortest dyadic length is 4, 8, 16, 16, 16 and then 32.")

    for length in (4, 8, 16):
        assert all(end != (0, 0) for end in endpoints(semidirect_step, (0, 0), length))
    word = "01320132032032032012012012012012"
    path = trace(semidirect_step, (0, 0), word)
    assert path[0] == path[-1] and len(set(path[:-1])) == 32
    print("C25 ⋊ C5 example: 500 vertices, shortest dyadic length 32.")


if __name__ == "__main__":
    main()
