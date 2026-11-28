"""Check regular K4 covers over A4 × (Z/17)^3 with independent abelian shifts."""

from collections import Counter
from itertools import permutations, product

CHORD = {(1, 2): 1, (2, 3): 2, (3, 1): 3, (2, 1): -1, (3, 2): -2, (1, 3): -3}
A4 = [p for p in permutations(range(4))
      if sum(p[i] > p[j] for i in range(4) for j in range(i+1, 4)) % 2 == 0]
MUL = [[A4.index(tuple(p[q[i]] for i in range(4))) for q in A4] for p in A4]
INV = [row.index(0) for row in MUL]


def directions(colors):
    return tuple(CHORD.get((i, j), 0) for i, j in zip(colors, colors[1:] + colors[:1]))


def balanced_words(length):
    words = set()

    def visit(path):
        if len(path) == length:
            if path[-1] == path[0] or path[-2] == path[0] or path[-1] == path[1]:
                return
            moves = directions(path)
            if any(moves.count(i) != moves.count(-i) for i in (1, 2, 3)):
                return
            # Starting point and orientation have no effect on existence of a simple lift.
            words.add(min(w[k:] + w[:k] for w in (path, path[::-1]) for k in range(length)))
            return
        for color in range(4):
            if color != path[-1] and (len(path) == 1 or color != path[-2]):
                visit(path + (color,))

    for first in range(4):
        visit((first,))
    return [(w, directions(w)) for w in sorted(words)]


def generates(marks):
    reached = {0}
    todo = [0]
    while todo:
        h = todo.pop()
        for a in marks:
            g = MUL[a][h]
            if g not in reached:
                reached.add(g)
                todo.append(g)
    return len(reached) == len(A4)


def simple_lift(word, moves, marks):
    abelian = [0, 0, 0]
    g = 0
    seen = set()
    for color, move in zip(word, moves):
        vertex = (color, g, *abelian)
        if vertex in seen:
            return False
        seen.add(vertex)
        if move:
            index = abs(move) - 1
            abelian[index] += 1 if move > 0 else -1
            a = marks[index]
            g = MUL[a if move > 0 else INV[a]][g]
    return g == 0 and abelian == [0, 0, 0]


def main():
    # Length ≤16 means no nonzero coordinate difference can be a multiple of 17.
    words = {k: balanced_words(k) for k in (4, 8, 16)}
    assert {k: len(v) for k, v in words.items()} == {4: 0, 8: 0, 16: 42}
    shortest = Counter()
    for marks in product(range(12), repeat=3):
        if generates(marks):
            length = next((k for k, paths in words.items()
                           if any(simple_lift(w, d, marks) for w, d in paths)), None)
            shortest[length] += 1
    assert shortest == {16: 1560}, shortest
    print("Every one of the 1,560 generating triples has shortest dyadic cycle length 16.")


if __name__ == "__main__":
    main()
