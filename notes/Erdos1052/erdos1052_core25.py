"""Exact finite checks for the odd-part exclusion at repeated core 25."""

from fractions import Fraction

from core_bounds_1052 import direct_small, forced, primes_through, uniform_gap
from erdos1052_fermat_bases import EXCLUDED_SINGLE_PRIME_VALUATIONS, check_valuations


def verify():
    assert forced(25) == (frozenset((7, 13)), 25, Fraction(32, 25))
    assert forced(25, 15) == (frozenset((3, 7, 13)), 5, Fraction(128, 75))
    gap = uniform_gap(25, 15, Fraction(199, 100), max_prime=4096, upper=2)
    assert gap == (13, 1555)
    assert Fraction(199, 100) * Fraction(201, 200) * (1 + Fraction(1, 2**20)) < 2
    witnesses = [p for p in primes_through(199) if p % 8 == 3 and p % 3 == 1 and p % 5 == 4]
    assert witnesses == [19, 139]
    assert [next(j for j in range(1, p) if pow(2, j, p) == 1) for p in witnesses] == [18, 138]
    assert Fraction(16, 15) * Fraction(64, 63) * Fraction(2048, 2047) < Fraction(6, 5)
    assert direct_small(25, 0, 49) == []
    assert all(forced(25, 2**h + 1) is None for h in (4, 8, 16, 32))
    check_valuations()
    assert EXCLUDED_SINGLE_PRIME_VALUATIONS == frozenset(range(6, 20))
    print('Core 25 checks passed. The only remaining exponents are powers of two with index at least 20 and squarefree composite Fermat number.')


if __name__ == '__main__':
    verify()
