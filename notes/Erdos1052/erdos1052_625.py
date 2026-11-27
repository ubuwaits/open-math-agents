"""Exact finite certificates for the classification of unitary perfect numbers with core 625.

Run beside core_bounds_1052.py and search_1052.py using Python 3.9 or later.
The proof that these finite checks cover arbitrarily large exponents is in
Erdős1052-core-625.txt. No primality oracle or floating point is used.
"""

from fractions import Fraction
from functools import lru_cache
from math import prod

from core_bounds_1052 import direct_small, forced, primes_through, uniform_gap
from search_1052 import factor


FIXED = frozenset((5, 79, 157, 313))
EPSILON = Fraction(1, 2048)


def odd_part(n):
    return n // (n & -n)


@lru_cache(maxsize=None)
def tail(x, D):
    # The odd Mersenne primes 2^k-1 below k=13 are exactly these four.
    # All finite products from k>=13 are bounded by 1/(1-2^-11).
    result = Fraction(2048, 2047)
    for q in (3, 7, 31, 127):
        if q > x:
            result *= Fraction(q + 1, q - 1)
    omega = sum(e for _, e in factor(D))
    return result * (1 + Fraction(2, x)) ** omega


def certify_group(h, j, excluded, cutoff=4096):
    """Exclude the relative 1/2048 interval around (5/4)^j for this group."""
    target = Fraction(5, 4) ** j
    low = target * (1 - EPSILON)
    high = target * (1 + EPSILON)
    primes = [q for q in primes_through(cutoff) if q not in FIXED and q not in excluded]
    nodes = largest = 0

    def check(x, D, ratio):
        nonlocal nodes, largest
        nodes += 1
        if ratio >= high:
            return
        assert ratio * tail(cutoff, D) < low
        left, right = x - 1, cutoff
        while right - left > 1:
            mid = (left + right) // 2
            if ratio * tail(mid, D) < low:
                right = mid
            else:
                left = mid
        y = right
        largest = max(largest, y)
        for q in primes:
            if q > y:
                break
            d = odd_part(q + 1)
            if x < q and D % d == 0:
                check(q, (D // d) * q, ratio * Fraction(q + 1, q))

    check(1, 5 ** h, Fraction(1))
    return nodes, largest


def classification():
    small_roots = [2 ** k - 1 for k in range(2, 13)
                   if factor(2 ** k - 1) == ((2 ** k - 1, 1),)]
    assert small_roots == [3, 7, 31, 127]
    for h, j, excluded in ((0, 1, {3}), (1, 1, {3, 7}), (1, 1, {3, 31}), (1, 2, {7, 31})):
        nodes, maximum = certify_group(h, j, excluded)
        print(f"h={h}, j={j}, excluding {sorted(excluded)}: {nodes} nodes, maximum cutoff {maximum}")
    # This checks every exponent below the start of the split-factor proof.
    assert direct_small(625, 0, 49) == [18]
    fixed, D, ratio = forced(625, 2 ** 18 + 1)
    assert D == 1 and ratio * (1 + Fraction(1, 2 ** 18)) == 2
    n = 2 ** 18 * 625 * prod(fixed)
    assert n == 146361946186458562560000
    # The prior results cover odd positive exponents and multiples of four.
    assert uniform_gap(625, 3, Fraction(1024, 513)) is not None
    for v in range(2, 6):
        assert forced(625, 2 ** (2 ** v) + 1) is None
    assert all(pow(2, 64 * k, p) != p - 1 for p in primes_through(1024)
               if p % 3 == 2 for k in range(p - 1))
    assert Fraction(1024, 513) * (1 + Fraction(1, 1024)) * (1 + Fraction(1, 2 ** 64)) < 2
    print(f"Only a=18, n={n}, at core 625.")


def sparse_cores():
    # Section 5 bounds the discarded contribution for any number of repeated primes.
    cutoff = 4096
    correction = 1 / ((1 - Fraction(1, cutoff ** 2)) * (1 - Fraction(3, cutoff - 1)))
    assert factor(65538) == ((2, 1), (3, 2), (11, 1), (331, 1))
    for a in range(1, 20):
        m = 2 ** (a & -a) + 1
        target = 2 / (1 + Fraction(1, 2 ** a))
        assert uniform_gap(1, m, target / correction, upper=target) is not None
    target = Fraction(1024, 513)
    for m in (3, 5, 17, 257, 65537, 641):
        assert uniform_gap(1, m, target, upper=2) is not None
    assert (2 ** 32 + 1) % 641 == 0
    possible_at_four = [p for p in primes_through(1024) if p % 3 == 2 and
                        any(pow(2, 16 * (2*k+1), p) == p-1 for k in range(p-1))]
    assert possible_at_four == [449] and 450 % 9 == 0
    assert target * correction * (1 + Fraction(1, 1024)) * (1 + Fraction(1, 2 ** 16)) < 2
    print("Verified the restrictions for arbitrary nonempty cores with sum of 1/p < 1/4096.")


if __name__ == "__main__":
    classification()
    sparse_cores()
