"""Certify intervals for ordinary-prime abundancies with fixed finite supplies.

The initial state is obtained by cancelling a divisor of the seed and the
unitary divisor sum of the core. A cutoff bounds the next explicit branch.
The reciprocal tail estimate covers primes of every size. Resource limits
return None and never contribute an exclusion.
"""

from fractions import Fraction
from functools import lru_cache
from heapq import heapreplace
from math import gcd, prod

from core_bounds_1052 import direct_small, forced
from erdos1052_fermat_bases import PATHS, SPLITS, check_valuations
from erdos1052_spectrum import passes_prime_test
from search_1052 import factor


def possible_starts(supplies, previous, ceiling, forbidden):
    """Generate shifts whose odd part is a divisor of the current supplies."""
    divisors = [(1, (), 0)]
    for p, e in supplies:
        extra = []
        for d, used, first in divisors:
            value = d
            for i in range(1, e+1):
                value *= p
                if 2*value > ceiling+1:
                    break
                extra.append((value, used+((p, i),), first or p))
        divisors.extend(extra)
    for d, used, first in divisors:
        # The least j>=1 with 2^j d > previous+1.
        j = max(1, ((previous+1)//d).bit_length())
        shifted = d << j
        while shifted <= ceiling+1:
            q = shifted-1
            if q not in forbidden and passes_prime_test(q):
                yield q, d, j, used, first
            shifted *= 2
            j += 1


@lru_cache(maxsize=300_000)
def path_coefficient(q, depth):
    """In units of 12^(-depth), bound (q+1) times a path's reciprocal loss."""
    if depth == 0:
        return 2
    scale = 12**depth
    # Every successor is 2*k*q-1. At k>=3 its coefficient divided by 2*k is <=1/3.
    future = scale//3
    for multiple in (2, 4):
        successor = multiple*q-1
        if passes_prime_test(successor):
            future = max(future, (12//multiple)*path_coefficient(successor, depth-1))
    return scale+future


def suffix_options(supplies, previous, ceiling, forbidden, target, gap,
                   path_depth=0, distinct_starts=False):
    """Bound all paths beginning at or above each candidate, including the infinite tail."""
    far = 8*(ceiling+1)
    scale = 1 << (far.bit_length()+24)

    def round_up(n, d):
        return (n*scale+d-1)//d

    counts = dict(supplies)
    outside = round_up(2, far+1)
    per_copy = dict.fromkeys(counts, outside)
    capacity = {p: [outside]*e for p,e in supplies} if distinct_starts else {}
    # Each large Mersenne start costs 2^(1-k). Sum over all k, including
    # composite exponents, with 2^k>far+1. Each frozen token can start one path.
    charge = round_up(4, 1 << (far+1).bit_length())
    charge += sum(e*per_copy[p] for p, e in supplies)
    candidates = []
    for row in sorted(possible_starts(supplies, previous, far, forbidden), reverse=True):
        q, _, _, used, first = row
        coefficient = path_coefficient(q, path_depth)
        divisor = (q+1)*12**path_depth
        cost = round_up(coefficient, divisor)
        if first:
            if distinct_starts:
                # A root uses every copy of its first frozen prime in d.
                # Split its charge equally among these copies. At most counts[p]
                # assigned copies can be present in an actual suffix.
                multiplicity = used[0][1]
                unit = round_up(coefficient, divisor*multiplicity)
                pool = capacity[first]
                for _ in range(multiplicity):
                    if unit <= pool[0]:
                        break
                    charge += unit-heapreplace(pool, unit)
            elif cost > per_copy[first]:
                charge += counts[first]*(cost-per_copy[first])
                per_copy[first] = cost
        else:
            charge += cost
        if q <= ceiling and charge*target >= gap*scale:
            candidates.append(row)
    return reversed(candidates)


def interval_gap(ratio, supplies, forbidden, low, high=Fraction(2), *,
                 max_bits=220, max_nodes=100_000, sharpen=True, path_depth=0, distinct_starts=False):
    """Return the node count and largest cutoff for a successful exact proof."""
    if not (0 < ratio and 0 < low <= high):
        raise ValueError('Positive rational endpoints and initial abundancy are required.')
    supplies = tuple(supplies)
    base_set = {p for p, _ in supplies}
    if len(base_set) != len(supplies) or any(p < 3 or p % 2 == 0 or e < 1 for p,e in supplies):
        raise ValueError('Supplies must have distinct odd bases and positive multiplicities.')
    stock_value = prod(p**e for p,e in supplies)
    scale = stock_value//gcd(stock_value, ratio.denominator)
    forbidden = frozenset(forbidden) | base_set
    nodes = largest = 0

    def visit(previous, stock, numerator, denominator):
        nonlocal nodes, largest
        nodes += 1
        if nodes > max_nodes:
            return False
        if numerator*high.denominator >= denominator*high.numerator:
            return True
        target = low.numerator*denominator
        gap = target - low.denominator*numerator
        if gap <= 0:
            return False
        copies = sum(e for _, e in stock)
        ceiling = max(previous, (2*copies+4)*target//gap + 1)
        if ceiling.bit_length() > max_bits:
            return False
        largest = max(largest, ceiling)
        if sharpen:
            rows = suffix_options(stock, previous, ceiling, forbidden, target, gap,
                                  path_depth, distinct_starts)
        else:
            rows = possible_starts(stock, previous, ceiling, forbidden)
        for q, d, j, used, _ in rows:
            used = dict(used)
            rest = tuple((p, e-used.get(p, 0)) for p, e in stock if e > used.get(p, 0))
            if not visit(q, rest+((q, 1),), numerator << j, denominator//d*q):
                return False
        return True

    return (nodes, largest) if visit(1, supplies, ratio.numerator*scale, ratio.denominator*scale) else None


@lru_cache(maxsize=None)
def core_state(core, seed):
    return forced(core, seed)


def core_gap(core, seed, bits, **limits):
    state = core_state(core, seed)
    if state is None:
        return 0, 0
    fixed, residual, ratio = state
    forbidden = fixed | set(dict(factor(core)))
    return interval_gap(ratio, factor(residual), forbidden, 2-Fraction(1, 2**bits), **limits)


# An interval at precision k excludes every exponent above k.
FIXED_CORES = {
    25: 44, 3025: 53, 180625: 53, 600625: 44, 845883: 53,
    2101707: 60, 7612947: 60, 14250625: 44, 21855625: 53,
    24750625: 60, 29597643: 53, 72675625: 53,
}

PATH_CORES = {243: 60, 58446025: 60, 99102025: 60}
PATH_LIMITS = dict(path_depth=2, distinct_starts=True, max_nodes=650_000, max_bits=350)


def fixed_core_certificates():
    """Also exclude arbitrary new repeated bases of total reciprocal mass <=2^(-k-6)."""
    totals = []
    for core, k in {**FIXED_CORES, **PATH_CORES}.items():
        limits = PATH_LIMITS if core in PATH_CORES else {}
        z = core_gap(core, 1, k, **limits)
        assert z is not None and direct_small(core, 0, k) == []
        bases = set(dict(factor(core)))
        t = Fraction(1, 2**(k+6))
        smooth = prod(Fraction(p, p-1) for p in bases)
        loss = t * (1 + 2*smooth/(1-t))
        keep = (1-loss)*(1-t*t)
        assert core+1 < 1/t and (1 << (k+2))+1 < 1/t
        assert keep > 1-Fraction(1, 2**(k+2))
        assert 2*keep/(1+Fraction(1, 2**(k+3))) > 2-Fraction(1, 2**k)
        small = []
        for a in range(1, k+3):
            seed = (1 << a)+1
            state = core_state(core, seed)
            target = Fraction(2*(seed-1), seed)
            if state is None:
                continue
            fixed, residual, ratio = state
            if ratio >= target:
                continue
            result = interval_gap(ratio, factor(residual), fixed | bases,
                                  target*(1-Fraction(1, 2**(k+2))), target, **limits)
            assert result is not None, (core, a)
            small.append(result[0])
        totals.append((core, k, z[0], len(small), sum(small)))
    return totals


def fermat_divisors(v, bound):
    """Superset of the primes r=2 mod 3 dividing F_v below an inclusive bound."""
    h = 1 << v
    step = 2*h
    first = 1 if step % 3 == 1 else 2
    for t in range(first, (bound-1)//step+1, 3):
        r = t*step+1
        if pow(2, h, r) == r-1:
            yield r


def synthetic_seed_certificates():
    """Remove one simple prime dividing a Fermat seed and reserve its factor of three."""
    counts = []
    for core, k, small_bound in ((819025, 28, 60), (11826721, 3, 60),
                                 (76125625, 5, 60), (75625, 43, 60), (12075625, 4, 64)):
        assert direct_small(core, 0, small_bound) == []
        # The six heights below 64 have a known divisor of the exact seed.
        for m in (3, 5, 17, 257, 65537, 641):
            assert core_gap(core, m, small_bound, **PATH_LIMITS) is not None
        assert core_gap(core, 3, k, **PATH_LIMITS) is not None
        # None of these core bases can be the required Fermat divisor at v>=6.
        assert all(p % 3 != 2 or (p-1) % 128 for p, _ in factor(core))
        cutoff = 1 << (k+2)
        assert Fraction(2, 1)/(1+Fraction(1, 1 << 64))/(1+Fraction(1, cutoff)) > (
            2-Fraction(1, 1 << k))
        start = 6
        if core == 75625:
            check_valuations()
            assert core % 3 and all(gcd(core, u*v) == 1 for u,v in SPLITS.values())
            assert all(gcd(core, prod(chain)) == 1 for chain in PATHS.values())
            start = 20
        small = [(v,r) for v in range(start, k+2) for r in fermat_divisors(v, cutoff)]
        assert all(core_state(core, r) is None for _,r in small)
        counts.append((core, len(small)))
    return counts


def double_exponent_certificate():
    """Check the two nearly equal factors of 2^(2b)+1 at core 5^4*181^2."""
    core = 20475625
    fixed, stock, ratio = core_state(core, 1)
    assert stock == 5**3*181**2
    assert direct_small(core, 0, 60) == []
    assert all(core_gap(core, m, 60, **PATH_LIMITS) for m in (3,17,257,65537,641))
    assert core_gap(core, 3, 7, **PATH_LIMITS)
    assert all(not list(fermat_divisors(v, 512)) for v in range(6,9))
    assert Fraction(2, 1)/(1+Fraction(1,1 << 64))/(1+Fraction(1,512)) > 2-Fraction(1,128)

    def normalized(d):
        return Fraction(d, 1 << (d.bit_length()-1))

    epsilon = Fraction(1, 1 << 45)
    assert 2*(1-epsilon) > 2/ratio
    divisors = sorted(5**i*181**j for i in range(4) for j in range(3))
    pairs = []
    for d in divisors[1:]:
        target = normalized(d)
        assert 1 < target*(1-epsilon) and target*(1+epsilon) < 2
        other = stock//d
        if d <= other and normalized(other)*target == 2/ratio:
            pairs.append((d,other))
    chosen = (5,25,181,4525)
    assert all(any(d in pair for d in chosen) for pair in pairs)
    results = []
    for d in chosen:
        target = normalized(d)
        result = interval_gap(Fraction(1), factor(d), fixed | {5,181},
                              target*(1-epsilon), target*(1+epsilon), **PATH_LIMITS)
        assert result is not None
        results.append(result[0])
    for t in (3,5,7,11,13,17,19,23,29,31):
        assert core_gap(core, (1 << (2*t))+1, 60, **PATH_LIMITS)
    witnesses = {37:593,41:10169,43:173,47:3761,53:15358129,59:1181,61:1709,
                 67:269,71:2845,73:293,79:317,83:4985,89:1069}
    assert set(witnesses) == {b for b in range(31,95,2) if all(p>31 for p,e in factor(b))}
    for b,m in witnesses.items():
        assert pow(2, 2*b, m) == m-1
        assert core_gap(core, m, 60, **PATH_LIMITS)
    return pairs, results


def core_139_certificate():
    """Exclude 3^5*139^2 and coprime extra bases of reciprocal sum at most 2^-86."""
    core = 3**5 * 139**2
    limits = dict(PATH_LIMITS, path_depth=3, max_nodes=2_000_000)
    gap = core_gap(core, 1, 80, **limits)
    assert gap is not None and direct_small(core, 0, 60) == []

    # Above 60 the divisors below suffice. At a=64 the required seed has
    # factor 274177. At odd a we use the wider gap because a may equal 61.
    seeds = (3, 5, 17, 257, 65537, 641, 274177)
    precision = {m: 55 if m == 3 else 60 for m in seeds}
    counts = {}
    for m in seeds:
        result = core_gap(core, m, precision[m], **limits)
        assert result is not None
        counts[m] = result[0]
    retained = 1-Fraction(1, 2**82)
    for a in range(61, 83):
        seed = (1 << a)+1
        target = Fraction(2*(seed-1), seed)
        assert any(seed % m == 0 and target*retained > 2-Fraction(1, 2**precision[m])
                   for m in seeds)

    mass = Fraction(1, 2**86)
    smooth = Fraction(3, 2)*Fraction(139, 138)
    loss = mass*(1+2*smooth/(1-mass))
    keep = (1-loss)*(1-mass**2)
    assert keep > retained and 2*keep/(1+Fraction(1, 2**83)) > 2-Fraction(1, 2**80)
    small = []
    for a in range(1, 61):
        seed = (1 << a)+1
        state = core_state(core, seed)
        target = Fraction(2*(seed-1), seed)
        if state is None or state[2] >= target:
            continue
        fixed, stock, ratio = state
        result = interval_gap(ratio, factor(stock), fixed | {3, 139},
                              target*retained, target, **limits)
        assert result is not None
        small.append(result[0])
    return gap[0], counts, len(small), sum(small)


if __name__ == "__main__":
    for row in fixed_core_certificates():
        print(*row, flush=True)
    print("Synthetic seed", synthetic_seed_certificates(), flush=True)
    print("Double exponent", double_exponent_certificate(), flush=True)
    print("The core 3^5*139^2", core_139_certificate(), flush=True)
