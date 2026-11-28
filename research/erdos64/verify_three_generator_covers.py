"""Verify shortest dyadic cycles in the rank-three class-two tetrahedral covers."""

from collections import Counter
from itertools import combinations
from math import gcd


CHORD = {(1, 2): 1, (2, 1): -1, (2, 3): 2, (3, 2): -2, (3, 1): 3, (1, 3): -3}


def step(vertex, new_color, modulus=None):
    color, x, y, z, xy, xz, yz = vertex
    move = CHORD.get((color, new_color), 0)
    sign = 1 if move > 0 else -1
    if abs(move) == 1:
        x, xy, xz = x + sign, xy + sign * y, xz + sign * z
    elif abs(move) == 2:
        y, yz = y + sign, yz + sign * z
    elif abs(move) == 3:
        z += sign
    coords = (x, y, z, xy, xz, yz)
    if modulus is not None:
        coords = tuple(t % modulus for t in coords)
    return (new_color, *coords)


def returns(length, modulus=None):
    for first in range(4):
        initial = (first, 0, 0, 0, 0, 0, 0)
        seen = {initial}

        def visit(vertex):
            if len(seen) == length:
                if vertex[0] != first:
                    yield step(vertex, first, modulus)[1:]
                return
            for color in range(4):
                if color == vertex[0]:
                    continue
                following = step(vertex, color, modulus)
                if following in seen:
                    continue
                seen.add(following)
                yield from visit(following)
                seen.remove(following)

        yield from visit(initial)


def trace(word, modulus=None):
    colors = [int(c) for c in word]
    path = [(colors[0], 0, 0, 0, 0, 0, 0)]
    for color in colors[1:] + colors[:1]:
        assert color != path[-1][0]
        path.append(step(path[-1], color, modulus))
    assert path[0] == path[-1] and len(set(path[:-1])) == len(word)
    return path[:-1]


def main():
    expected = {4: {1: 24}, 8: {1: 498, 2: 54},
                16: {1: 142914, 2: 4734, 3: 288, 4: 72}}
    for length, counts in expected.items():
        actual = Counter(gcd(*end) for end in returns(length))
        assert actual == counts, (length, actual)
        print(f"Length {length}, integral return-coordinate gcds: {actual}")

    large_word = '01321021023123102102132012012012'
    ring = trace(large_word)
    collisions = Counter(gcd(*(a - b for a, b in zip(u[1:], v[1:])))
                         for u, v in combinations(ring, 2) if u[0] == v[0])
    assert collisions == {1: 107, 2: 14, 3: 3}

    witnesses = {1: '0123', 2: '0120123103120123', 3: '0120120123023023', 4: large_word}
    for modulus, word in witnesses.items():
        trace(word, modulus)
        for length in (4, 8, 16):
            if length < len(word):
                assert all(any(end) for end in returns(length, modulus)), (modulus, length)
    print('Shortest dyadic length: 4 at n=1, 16 at n=2,3, and 32 for all n>=4.')


if __name__ == '__main__':
    main()
