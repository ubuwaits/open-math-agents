"""Compute necessary odd-exponent bounds for a factored, nonempty sparse core.

Run with no arguments for the worked example, or pass prime powers as p^e,
for example: python3 -B erdos1052_odd_part.py 65537^16
"""

import argparse
from collections import Counter
from fractions import Fraction
from math import gcd, prod

from core_bounds_1052 import uniform_gap
from erdos1052_fermat_bases import CORE_SHIFT_PATHS, allows_valuation, can_absorb_path
from search_1052 import factor


FERMAT_SHIFT_DIVISORS = {
    7: 14379237889, 8: 2478250459649, 9: 70657, 10: 341114881,
    11: 730882049, 12: 4513793, 15: 3604481, 17: 786433,
    18: 2967994369, 20: 211812353, 23: 3238002689,
}


def forced_shift_conflict(powers, seed):
    """Test the odd factors forced by one known prime divisor of a core shift."""
    pending = Counter({seed: 1})
    while pending:
        p = max(pending)
        demand = pending.pop(p)
        if demand > powers.get(p, 1):
            return True
        if p not in powers:
            pending.update({q: e for q, e in factor(p + 1) if q != 2})
    return False


def prime_order(base, prime):
    order = prime - 1
    for divisor, _ in factor(order):
        while order % divisor == 0 and pow(base, order // divisor, prime) == 1:
            order //= divisor
    return order


def bounds(powers):
    if not powers or any(p <= 2 or factor(p) != ((p, 1),) or e < 2
                         for p, e in powers.items()):
        raise ValueError("Each component must be an odd prime to an exponent of at least two.")
    if sum(Fraction(1, p) for p in powers) >= Fraction(1, 4096):
        raise ValueError("This bound requires the reciprocal sum to be below 1/4096.")
    if any((p % 3 == 2 and e % 2) or (p == 65537 and e % 16) for p, e in powers.items()):
        return []
    if any(pow(p, e, m) == m - 1 for p, e in powers.items() for m in (3, 5, 17, 257)):
        return []
    if 167772161 in powers:
        e = powers[167772161]
        chain = CORE_SHIFT_PATHS.get((e & -e).bit_length()-1)
        if chain is not None and not can_absorb_path(powers, chain):
            return []
    if 65537 in powers:
        e = powers[65537]
        two_part = e & -e
        if two_part in (32, 64) or (two_part == 16 and 4365089 not in powers):
            return []
        witness = FERMAT_SHIFT_DIVISORS.get(two_part.bit_length() - 1)
        if witness is not None and forced_shift_conflict(powers, witness):
            return []

    vs = set()
    for p in powers:
        if p % 3 == 2:
            order = prime_order(2, p)
            if order & (order - 1) == 0:
                v = order.bit_length() - 2
                if v >= 6 or (v == 4 and 65537 in powers):
                    vs.add(v)
    vs = {v for v in vs if allows_valuation(powers, v)}
    if not vs:
        return []
    core = prod(p**e for p, e in powers.items())
    sigma = 1
    for p, e in powers.items():
        sigma = sigma * (pow(p, e, core) + 1) % core
    result = []
    for v in sorted(vs):
        h = 2**v
        # c is odd, so removing powers of two from sigma leaves this gcd unchanged.
        g = gcd(core, sigma * (pow(2, h, core) + 1))
        left = core // g
        k = 0
        for p in powers:
            while left % p == 0:
                left //= p
                k += 1
        assert left == 1
        choices = []
        for p, _ in factor(h + 1):
            for q, _ in factor(h * p + 1):
                m = prime_order(p, q)
                p_stride = 1 if p == 3 else m + int(q == h * p + 1)
                choices.append((max(p - 1, p_stride) * k, p, q, m))
        omega_bound, p, q, m = min(choices)
        omega_bound = min(omega_bound, 2 * k)
        result.append((v, k, omega_bound, p, q, m))
    return result


def checks():
    correction = 1 / ((1 - Fraction(1, 4096**2)) * (1 - Fraction(3, 4095)))
    target = Fraction(1024, 513)
    assert target * correction * (1 + Fraction(1, 2**16)) < 2
    for m in (3, 5, 17, 257):
        assert uniform_gap(1, m, target, upper=2) is not None
        assert 65537 % m == 2
    for missing, certificate in ((3, (1, 3)), (5, (25, 398)), (7, (3, 14))):
        assert uniform_gap(1, 1, target, upper=2, allowed=lambda q: q != missing) == certificate
    for j, r in ((4, 4365089), (5, 1409), (6, 641)):
        assert factor(r) == ((r, 1),) and pow(65537, 2**j, r) == r-1
    assert 4365090 % 9 == 0 and 1410 % 15 == 0 and 642 % 107 == 0 and 108 % 9 == 0
    assert pow(2, 8, 11) == 3 and all(pow(2, 4*i, 10) == 6 for i in range(1, 6))
    for j, r in FERMAT_SHIFT_DIVISORS.items():
        assert factor(r) == ((r, 1),) and pow(65537, 2**j, r) == r - 1
        assert forced_shift_conflict({65537: 2**j}, r)
        assert bounds({65537: 2**j}) == []
    assert all(bounds({65537: e}) == [] for e in range(2, 8192))
    for t in range(5):
        m = 2**(16 * 3**t) + 1
        assert m % 65537 == 0 and (m // 65537) % 65537 != 0
        y = 2**(16 * 3**t)
        assert gcd(y+1, y*y-y+1) == 1
        assert (y+1)*(y*y-y+1) == y**3+1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("powers", nargs="*", metavar="p^e", default=["65537^16"])
    args = parser.parse_args()
    try:
        components = [tuple(map(int, item.split("^"))) for item in args.powers]
        if any(len(pair) != 2 for pair in components) or len(dict(components)) != len(components):
            raise ValueError("Use one p^e entry per prime.")
        result = bounds(dict(components))
    except ValueError as error:
        parser.error(str(error))
    if not args.powers or args.powers == ["65537^16"]:
        checks()
    if not result:
        print("These necessary conditions rule out every exponent at this core.")
    for v, k, count, p, q, m in result:
        if k == 0:
            print(f"v2(a) = {v}: b must equal 1, so only a = {2**v} is possible.")
        else:
            print(f"v2(a) = {v}, K = {k}. The exponent of 3 plus the number of other "
                  f"distinct primes in b is at most {k}. Omega(b) <= {count}. "
                  f"The number of distinct primes in b is at most {(k + 2).bit_length() - 1}.")
