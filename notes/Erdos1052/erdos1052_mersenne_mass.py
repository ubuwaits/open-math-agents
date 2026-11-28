"""Exact interval certificates for Mersenne residuals with dyadic weighted sum."""

from collections import Counter
from fractions import Fraction
from itertools import combinations

from erdos1052_chain_bounds import group_windows
from erdos1052_spectrum import exclude_interval


def exp_minus(x, degree):
    """Odd and even Taylor polynomials bound exp(-x) from below and above."""
    term = total = Fraction(1)
    for j in range(1, degree + 1):
        term *= -x / j
        total += term
    return total


def finite_mass_certificate():
    """Check 0 <= m <= 37 and h >= m, outside the two stated exceptions."""
    counts = Counter()
    windows = group_windows()
    large_prime_loss = Fraction(1, 1 << 75)

    def test(m, subset, h, scale, on, off, rest, mass, known, fixed, coarse):
        required_mass = sum(Fraction(1, 1 << k) for k in rest)
        if mass < required_mass:
            return
        largest_x = Fraction(1, 1 << (rest[0] if rest else 79))
        y = Fraction(1, 1 << h)
        # h=64 represents all h >= 64. The true correction is strictly > 1.
        correction = (1+y)/(1+y**3) if h == 16 else Fraction(1)
        bottom, top = windows[on, off]
        low = max(bottom, scale * known * exp_minus(mass/(1-largest_x), 13)
                  * correction * (1-large_prime_loss))
        high = min(top, scale * known * exp_minus(mass, 14) * (1+y))
        if low >= high:
            return

        bases = tuple((1 << k)-1 for k in subset)
        supplies = None
        if not coarse:
            supplies = {(1 << k)-1: e for k, e in fixed}
            supplies.update({(1 << k)-1: int(mass*(1 << k)) for k in rest})
        result = exclude_interval(low, high, bases, on, forbidden=off,
                                  multiplicities=supplies, sharpen_tail=True,
                                  bit_cap=210 if coarse else 260,
                                  node_cap=4500 if coarse else 15000)
        counts["tests"] += 1
        if result is not None:
            counts["certificates"] += 1
            counts["nodes"] += result[0]
            return
        if coarse:
            test(m, subset, h, scale, on, off, rest, mass, known, fixed, False)
            return
        if not rest or rest[0] > 19:
            raise ArithmeticError(f"Unresolved at {(m, subset, h, on, off, fixed)}")
        k = rest[0]
        x = Fraction(1, 1 << k)
        maximum = int((mass-required_mass+x)/x)
        counts["splits"] += 1
        for e in range(1, maximum + 1):
            test(m, subset, h, scale, on, off, rest[1:], mass-e*x,
                 known*(1-x)**e, fixed+((k, e),), False)

    for m in range(38):
        mass = Fraction(1, 1 << m)
        small = [k for k in (13, 17, 19, 31, 61) if k >= m]
        for size in range(len(small) + 1):
            for subset in combinations(small, size):
                for h in (16, 64):
                    if h < m:
                        continue
                    if ((m, h) in ((14, 64), (15, 16))
                            and 13 not in subset and {17, 19}.issubset(subset)):
                        counts["excepted families"] += 1
                        continue
                    bases = {(1 << k)-1 for k in subset}
                    for scale in (2, 4):
                        for on, off in windows:
                            if bases.isdisjoint(on):
                                test(m, subset, h, scale, on, off, subset, mass,
                                     Fraction(1), (), True)
    return dict(sorted(counts.items()))


def exact_pair_certificate():
    """In (11) the two mandatory bases cannot constitute the whole residual."""
    windows = group_windows()
    p, r = (1 << 17)-1, (1 << 19)-1
    checks = nodes = 0
    for m, heights in ((14, (64, 128)), (15, (16,))):
        for e in range(1, 1 << (17-m)):
            f = (1 << (19-m))-4*e
            normalized = 2*Fraction(p, p+1)**e*Fraction(r, r+1)**f
            for h in heights:
                y = Fraction(1, 1 << h)
                correction = (1+y)/(1+y**3) if h < 128 else Fraction(1)
                for (on, off), (bottom, top) in windows.items():
                    low = max(bottom, normalized*correction)
                    high = min(top, normalized*(1+y))
                    if low >= high:
                        continue
                    result = exclude_interval(low, high, (p, r), on, forbidden=off,
                                              multiplicities={p: e, r: f}, sharpen_tail=True,
                                              bit_cap=420, node_cap=200000)
                    if result is None:
                        raise ArithmeticError(f"Unresolved exact pair at {(m, h, e, f, on)}")
                    checks += 1
                    nodes += result[0]
    return checks, nodes


if __name__ == "__main__":
    print(finite_mass_certificate())
    print("Exact two-base intervals and nodes", exact_pair_certificate())
