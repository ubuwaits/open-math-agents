"""Compute the modified Dedekind-psi height and its fixed-core bound."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import prod

from search_1052 import factor, odd_powerful_numbers


@lru_cache(maxsize=None)
def height(n):
    if n < 1:
        raise ValueError("The additive height is defined on positive integers.")
    return sum(e*prime_height(p) for p,e in factor(n))


@lru_cache(maxsize=None)
def prime_height(p):
    return 1 if p == 2 else 1+height((p+1)//2)


def core_budget(c):
    return 1+height(c)-sum(height(p**e+1) for p,e in factor(c))


def mixed_indices(b):
    """Count nontrivial divisors with an even number of distinct primes."""
    exponents = [e for _,e in factor(b)]
    return (prod(1+e for e in exponents)+prod(1-e for e in exponents))//2-1


@lru_cache(maxsize=None)
def mersenne_leaves(p):
    """Return pairs (Mersenne exponent, multiplicity) below an odd prime."""
    odd_children = [(q, e) for q, e in factor(p+1) if q != 2]
    if not odd_children:
        return ((p.bit_length(), 1),)
    counts = Counter()
    for q, e in odd_children:
        for k, multiplicity in mersenne_leaves(q):
            counts[k] += e*multiplicity
    return tuple(sorted(counts.items()))


def residual_leaf_mass(residual, h):
    """Exact value of U for the terminal divisor and sparse height in section 8."""
    if residual < 1 or residual % 2 == 0 or h < 1:
        raise ValueError('A positive odd residual and a positive height are required.')
    mass = Fraction()
    for p, e in factor(residual):
        leaves = mersenne_leaves(p)
        if all(k > h for k, _ in leaves):
            mass += sum(Fraction(e*count, 2**(k-1)) for k, count in leaves)
    return mass


def can_repeat_a_leaf(c):
    """Whether the core supplies room for a repeated Mersenne leaf in the seed."""
    bases = dict(factor(c))
    difference = Counter()
    for p, e in bases.items():
        for k, count in mersenne_leaves(p):
            difference[k] += e*count
        for q, power in factor(p**e+1):
            if q != 2:
                for k, count in mersenne_leaves(q):
                    difference[k] -= power*count
    return any(count > int(2**k-1 in bases) for k, count in difference.items())


if __name__ == "__main__":
    histogram = Counter(core_budget(c) for c in odd_powerful_numbers(10**8))
    assert sum(histogram.values()) == 7857
    assert max(histogram) == 6 and sum(n for k,n in histogram.items() if k < 1) == 2229
    assert core_budget(1) == 1 and core_budget(625) == 3
    assert core_budget(65537**2) == 1 and height(65537)-16 == 2
    assert residual_leaf_mass(65537, 16) == 0
    assert residual_leaf_mass(131071**2, 16) == Fraction(2, 2**16)
    assert sum(not can_repeat_a_leaf(c) for c in odd_powerful_numbers(10**8)) == 1236
    for a in range(1,53):
        h = a & -a
        assert height(2**a+1)-a >= height(2**h+1)-h+mixed_indices(a//h)
    print("Fixed-core height budgets through 10^8", sorted(histogram.items()))
