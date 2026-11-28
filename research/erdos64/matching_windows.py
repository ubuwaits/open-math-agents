"""Check the Heisenberg lower bounds in the contracted bipartite multigraph."""
from collections import Counter
from math import gcd


def matching_step(sheet, port, outward):
    x, y, z = sheet
    direction = 1 if outward else -1
    if port == 1:
        return x + direction, y, z + direction * y
    if port == 2:
        return x, y - direction, z
    return sheet


def return_counts(length):
    counts = Counter()

    def extend(word, position):
        if len(word) == length:
            if word[-1] != word[0]:
                counts[gcd(*position)] += 1
            return
        for port in range(3):
            if not word or word[-1] != port:
                extend((*word, port), matching_step(position, port, len(word) % 2 == 0))

    extend((), (0, 0, 0))
    return dict(sorted(counts.items()))


if __name__ == '__main__':
    # A word closes modulo n exactly when n divides the gcd of its final coordinates.
    expected = {
        2: {1: 6},
        4: {1: 14, 2: 4},
        8: {1: 236, 2: 18, 4: 4},
        10: {1: 830, 2: 150, 3: 30, 4: 10, 5: 6},
    }
    for length, wanted in expected.items():
        actual = return_counts(length)
        assert actual == wanted, (length, actual)
        print(f"Matching length {length}, return-coordinate gcds: {actual}")
