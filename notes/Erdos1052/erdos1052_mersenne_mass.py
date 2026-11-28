"""Exact interval certificates for the Mersenne residual divisor."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import prod

from erdos1052_chain_bounds import group_windows
from erdos1052_spectrum import exclude_interval, passes_prime_test


def exp_minus(x, degree):
    """Odd and even Taylor polynomials bound exp(-x) from below and above."""
    term = total = Fraction(1)
    for j in range(1, degree + 1):
        term *= -x / j
        total += term
    return total


def cubefree_certificate(*, mixed=False):
    """Test cubefree Mersenne residuals near two, or both scales with Fermat bases."""
    candidates = [(k,-1) for k in (13,17,19,31,61)]
    if mixed:
        candidates.insert(1,(16,1))
    windows = group_windows()
    tail = Fraction(1,1 << (75 if mixed else 76))
    # Each k >= 79 contributes at most 2/(2^k-1) to the deletion loss.
    # Bound 1/(2^k-1) by 2/(2^k), and sum even the composite indices.
    assert 4*Fraction(2,1 << 79) == Fraction(1,1 << 76)
    assert 4*Fraction(2,1 << 79)+4*Fraction(1,1 << 128) < Fraction(1,1 << 75)
    checks = nodes = 0
    for counts in product(range(3),repeat=len(candidates)):
        supplies = {(1 << k)+s:e for (k,s),e in zip(candidates,counts) if e}
        mass = sum(Fraction(e,1 << k) for (k,_),e in zip(candidates,counts))
        retained = prod((Fraction((1 << k)+s,1 << k)**e
                         for (k,s),e in zip(candidates,counts)),start=Fraction(1))
        for h in (16,64):
            y = Fraction(1,1 << h)
            if not mixed and h == 16 and mass+tail < y:
                continue
            if mixed and h == 64 and not supplies:
                continue
            correction = (1+y)/(1+y**3) if h == 16 else Fraction(1)
            for scale in ((1,2) if mixed else (2,)):
                lower = scale*retained*(1-tail)**2*correction
                upper = scale*retained*(1+y)
                if mixed:
                    upper /= 1-tail
                for (on,off),(bottom,top) in windows.items():
                    if not supplies.keys().isdisjoint(on):
                        continue
                    low,high = max(bottom,lower),min(top,upper)
                    if low >= high:
                        continue
                    result = exclude_interval(low,high,supplies,on,forbidden=off,
                                              multiplicities=supplies,sharpen_tail=True,
                                              bit_cap=250,node_cap=16000)
                    if result is None:
                        raise ArithmeticError(f"Unresolved at {counts}, h={h}, required={on}")
                    checks += 1
                    nodes += result[0]
    return checks,nodes


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


@lru_cache(maxsize=None)
def third_factor_bounds(mass, k, tail):
    """Enclose the residual product with all its remaining mass at k or above."""
    x = Fraction(1, 1 << k)
    # -log(1-x)/x has positive coefficients. Its degree-five remainder
    # is at most x^6/(7*(1-x)). In a tail each x_p may be smaller than x.
    lower_log = sum(x**i / (i+1) for i in range(6))
    upper_log = lower_log+x**6/(7*(1-x))
    low = exp_minus(mass*upper_log, 31)
    high = exp_minus(mass*(1 if tail else lower_log), 32)
    if tail:
        # Remove all vertices using any base at exponent k or larger.
        low *= 1-Fraction(16, 1 << k)
    return low, high


def round_outward(low, high, bits=320):
    denominator = 1 << bits
    return (Fraction((low.numerator*denominator)//low.denominator, denominator),
            Fraction(-((-high.numerator*denominator)//high.denominator), denominator))


def exact_third_certificate():
    """Exclude a single third base of any size, or any mixture entirely beyond k=255."""
    windows = group_windows()
    cutoff = 256
    exponents = [k for k in range(31, cutoff, 2) if passes_prime_test((1 << k)-1)]
    assert exponents == [31, 61, 89, 107, 127]
    p, r = (1 << 17)-1, (1 << 19)-1
    checks = nodes = 0
    for k in [cutoff]+exponents:
        for m, heights in ((15, (16,)), (14, (64, 128, 256, 512))):
            for e in range(1, 1 << (17-m)):
                for f in range(1, (1 << (19-m))-4*e):
                    mass = Fraction(1, 1 << m)-Fraction(e, 1 << 17)-Fraction(f, 1 << 19)
                    known = 2*Fraction(p, p+1)**e*Fraction(r, r+1)**f
                    supplies = {p: e, r: f}
                    if k < cutoff:
                        supplies[(1 << k)-1] = int(mass*(1 << k))
                    low_u, high_u = third_factor_bounds(mass, k, k == cutoff)
                    for h in heights:
                        y = Fraction(1, 1 << h)
                        # A positive remaining mass is at least 2^-19, so
                        # log2 D > 122880 and the binary exponent exceeds 600.
                        correction = (1+y)/(1+Fraction(1, 1 << 600)) if h < 512 else Fraction(1)
                        low, high = round_outward(known*low_u*correction, known*high_u*(1+y))
                        for (on, off), (bottom, top) in windows.items():
                            lo, hi = max(bottom, low), min(top, high)
                            if lo >= hi:
                                continue
                            result = exclude_interval(lo, hi, tuple(supplies), on, forbidden=off,
                                                      multiplicities=supplies, sharpen_tail=True,
                                                      bit_cap=450, node_cap=30000)
                            if result is None:
                                raise ArithmeticError(f"Unresolved third factor at {(m, h, k, e, f, on)}")
                            checks += 1
                            nodes += result[0]
    return checks, nodes


def mixed_mass_certificate():
    """Exclude h=16, and at larger heights require a base with exponent 31 or 61."""
    windows = group_windows()
    p, r = (1 << 17)-1, (1 << 19)-1
    counts = Counter()

    def test(mass, known, e, f, h, allocation, present, cutoff, loss):
        x = Fraction(1, 1 << (present[0] if present else cutoff))
        supplies = {p: e, r: f}
        supplies.update({(1 << k)-1: int(mass*(1 << k)) for k in present})
        y = Fraction(1, 1 << h)
        correction = (1+y)/(1+Fraction(1, 1 << 600)) if h < 512 else Fraction(1)
        low, high = round_outward(known*exp_minus(mass/(1-x), 25)*correction*(1-loss),
                                  known*exp_minus(mass, 26)*(1+y))
        bottom, top = windows[allocation]
        low, high = max(bottom, low), min(top, high)
        if low >= high:
            return True
        on, off = allocation
        result = exclude_interval(low, high, tuple(supplies), on, forbidden=off,
                                  multiplicities=supplies, bit_cap=420, node_cap=30000,
                                  sharpen_tail=True)
        if result is None:
            return False
        counts["certificates"] += 1
        counts["nodes"] += result[0]
        return True

    for m, heights in ((15, (16,)), (14, (64, 128, 256, 512))):
        small_options = ((), (31,), (61,), (31, 61)) if m == 15 else ((),)
        for e in range(1, 1 << (17-m)):
            for f in range(1, (1 << (19-m))-4*e):
                mass = Fraction(1, 1 << m)-Fraction(e, 1 << 17)-Fraction(f, 1 << 19)
                known = 2*Fraction(p, p+1)**e*Fraction(r, r+1)**f
                for small in small_options:
                    for h in heights:
                        for allocation in windows:
                            args = mass, known, e, f, h, allocation
                            if test(*args, small, 79, Fraction(1, 1 << 75)):
                                continue
                            counts["refinements"] += 1
                            for size in range(4):
                                for extra in combinations((89, 107, 127), size):
                                    if not test(*args, small+extra, 256, Fraction(16, 1 << 256)):
                                        raise ArithmeticError(
                                            f"Unresolved mixture at {(m, h, e, f, small, extra, allocation)}")
    return dict(sorted(counts.items()))


if __name__ == "__main__":
    print("Cubefree Mersenne intervals and nodes", cubefree_certificate(), flush=True)
    print("Cubefree mixed intervals and nodes", cubefree_certificate(mixed=True), flush=True)
    print(finite_mass_certificate())
    print("Exact two-base intervals and nodes", exact_pair_certificate())
    print("Third-base intervals and nodes", exact_third_certificate())
    print("Mixed-base exclusions", mixed_mass_certificate())
