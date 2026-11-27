"""Exact exponent certificate for the sparse prime-power base 167772161.

The parameter limits the exponent e of the odd core p^e. The odd multiplier
of v2(n) and the simple primes of n range over all sizes. The argument is in
Erdős1052-prime-square.txt. Run without arguments for the full certificate.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import product

from core_bounds_1052 import uniform_gap
from erdos1052_sparse_parents import allowed


P = 167772161
H = 1 << 23
PRECISION = 96
EPSILON = Fraction(1, 1 << PRECISION)
OPEN_PADDING = Fraction(1, 1 << 110)
CUTOFF = 262144
FINAL_CUTOFF = 1 << 26
SUPPLIERS = ((19, 223), (19, 433), (79, 13), (79, 223))
CLOSURES = {19: {3, 5, 19}, 79: {3, 5, 79}, 13: {7, 13},
            223: {7, 223}, 433: {7, 31, 433}}
MARKERS = (31, 127, 8191, 131071, 524287)


def normalized_intervals(low, high, uses):
    """Enclose the normalized group, then account for removal of p-using paths."""
    retained = 1 - min(Fraction(3, P-1), Fraction(uses, 2*P))
    result = []
    for scale in (Fraction(1, 2), 1, 2):
        lower, upper = low*scale, high*scale
        if upper >= 1 and lower < 2:
            result.append((max(1, lower)*retained, min(2, upper+OPEN_PADDING)))
    return tuple(result)


def group_intervals(cap):
    # The three dictionaries are indexed respectively by i, j, and i+j.
    quotient = {0: ((Fraction(1), 1+OPEN_PADDING),)}
    fermat, core_shift = {}, {}
    scale = 1 << PRECISION
    power = 1
    for index in range(1, cap+1):
        power *= P
        exponent = power.bit_length()-1
        if exponent <= PRECISION:
            low = high = Fraction(power, 1 << exponent)
        else:
            leading = power >> (exponent-PRECISION)
            low, high = Fraction(leading, scale), Fraction(leading+1, scale)
        # H > PRECISION, and p^e > 2^PRECISION whenever 32 divides e.
        quotient[index] = normalized_intervals(low, high*(1+EPSILON), index)
        fermat[index] = normalized_intervals(low/(1+EPSILON), high, index-1)
        core_shift[index] = normalized_intervals(2/high/(1+EPSILON), 2/low, cap)
    return quotient, fermat, core_shift


@lru_cache(maxsize=100000)
def possible(intervals, cutoff, required, forbidden):
    def permitted(q):
        return allowed(q) and q not in forbidden

    return any(uniform_gap(1, 1, lo, cutoff, upper=hi, allowed=permitted,
                           required=required) is None for lo, hi in intervals)


def minimal_masks(rows):
    feasible = {}
    for index, intervals in rows.items():
        masks = []
        for mask in range(8):
            if any(previous & mask == previous for previous in masks):
                continue
            banned = tuple(q for q, bit in ((3, 1), (5, 1), (7, 2), (31, 4))
                           if not bit & mask)
            if possible(intervals, 65536, (), banned):
                masks.append(mask)
        if masks:
            feasible[index] = masks
    return feasible


def admissible_allocation(intervals, quotient_present, cutoff=CUTOFF, suppliers=SUPPLIERS):
    groups = range(3)
    recipients = groups if quotient_present else range(1, 3)

    def place_markers(required, forbidden, remaining):
        if any(not possible(bounds, cutoff, tuple(sorted(need)), tuple(sorted(ban)))
               for bounds, need, ban in zip(intervals, required, forbidden)):
            return False
        if not remaining:
            return True
        q, *rest = remaining
        if any(q in group for group in required):
            return place_markers(required, forbidden, rest)
        if place_markers(required, [ban | {q} for ban in forbidden], rest):
            return True
        for owner in recipients:
            if q in forbidden[owner]:
                continue
            needs = [need | ({q} if g == owner else set()) for g, need in enumerate(required)]
            bans = [ban | ({q} if g != owner else set()) for g, ban in enumerate(forbidden)]
            if place_markers(needs, bans, rest):
                return True
        return False

    for supplier5, supplier7 in suppliers:
        first, second = CLOSURES[supplier5], CLOSURES[supplier7]
        for owner5, owner7 in product(recipients, repeat=2):
            need = [(first if g == owner5 else set()) | (second if g == owner7 else set())
                    for g in groups]
            banned = [(first | second)-group for group in need]
            if place_markers(need, banned, MARKERS):
                return True
    return False


def large_base_suppliers():
    """Any single repeated base p >= 2^17 has suppliers 19 and 223."""
    base = 1 << 17
    target = 2-Fraction(1, 1 << 14)
    error = (1+Fraction(1, base**2))/(1-Fraction(3, base-1))
    assert target * error * (1+Fraction(1, 1 << 64)) < 2
    for s, t in SUPPLIERS[1:]:
        assert uniform_gap(1, 1, target, 65536, upper=2, allowed=allowed,
                           required=(3, 5, 7, s, t)) is not None
    return ((19, 223),)


def scan(cap):
    assert H > PRECISION and P**32 > 1 << PRECISION
    assert P % 3 == 2 and pow(2, H, P) == P-1
    a, f, c = group_intervals(cap)
    ma, mf, mc = map(minimal_masks, (a, f, c))
    candidates = []
    survivors = []
    suppliers = large_base_suppliers()
    for n in sorted(mc):
        for j in mf:
            if j > n:
                break
            i = n-j
            if i not in ma:
                continue
            if not any(not (x & y or x & z or y & z)
                       for x, y, z in product(ma[i], mf[j], mc[n])):
                continue
            intervals = (a[i], f[j], c[n])
            if admissible_allocation(intervals, i > 0):
                candidates.append((i, j))
                if admissible_allocation(intervals, i > 0, FINAL_CUTOFF, suppliers):
                    survivors.append((i, j))
    return candidates, survivors


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cap", type=int, nargs="?", default=8192, choices=range(1, 8193),
                        metavar="1..8192")
    cap = parser.parse_args().cap
    candidates, survivors = scan(cap)
    expected = [602, 1206, 3482, 5169, 5249, 7445, 8049, 8129]
    assert candidates == [(0, j) for j in expected if j <= cap]
    assert not survivors
    print(f"Checked all core exponents through {cap}. All {len(candidates)} "
          "allocations reaching the final interval test were excluded.")
