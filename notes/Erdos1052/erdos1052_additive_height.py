"""Compute the modified Dedekind-psi height and its fixed-core bound."""

from collections import Counter
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


if __name__ == "__main__":
    histogram = Counter(core_budget(c) for c in odd_powerful_numbers(10**8))
    assert sum(histogram.values()) == 7857
    assert max(histogram) == 6 and sum(n for k,n in histogram.items() if k < 1) == 2229
    assert core_budget(1) == 1 and core_budget(625) == 3
    assert core_budget(65537**2) == 1 and height(65537)-16 == 2
    for a in range(1,53):
        h = a & -a
        assert height(2**a+1)-a >= height(2**h+1)-h+mixed_indices(a//h)
    print("Fixed-core height budgets through 10^8", sorted(histogram.items()))
