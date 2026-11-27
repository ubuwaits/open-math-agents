"""Certify the possible primes supplying 5 and 7 at any nonempty sparse core.

The inequalities are exact. Each successful interval certificate covers all
primes by the tail bound in Erdős1052-core-bounds.txt.
"""

from fractions import Fraction
from itertools import product

from core_bounds_1052 import forced, primes_through, uniform_gap


def allowed(p):
    return p in (3, 5) or p % 3 == 1


def path_bound(p):
    return Fraction(p + 1, p - 1)


def gap(m, loss=1):
    correction = 1 / ((1 - Fraction(1, 4096**2)) * (1 - Fraction(3, 4095)))
    retained_lower = 2 / ((1 + Fraction(1, 2**16)) * correction)
    return uniform_gap(1, m, retained_lower / loss, 65536, upper=2, allowed=allowed)


def parent_options(s, cutoff):
    assert gap(s, path_bound(cutoff)) is not None
    options = []
    for q in primes_through(cutoff - 1):
        if q <= s or (q + 1) % s or not allowed(q):
            continue
        state = forced(1, q)
        if state is None or not all(map(allowed, state[0])):
            continue
        if gap(q, path_bound(2 * q - 1)) is None:
            options.append(q)
    return options


def check():
    parents_5 = parent_options(5, 554)
    parents_7 = parent_options(7, 1040)
    assert parents_5 == [19, 79]
    assert parents_7 == [13, 223, 433]
    pairs = []
    for p, q in product(parents_5, parents_7):
        assert forced(1, p)[0].isdisjoint(forced(1, q)[0])
        if gap(p * q, path_bound(2 * p - 1) * path_bound(2 * q - 1)) is None:
            pairs.append((p, q))
    assert pairs == [(19, 223), (19, 433), (79, 13), (79, 223)]
    return pairs


if __name__ == "__main__":
    print(check())
