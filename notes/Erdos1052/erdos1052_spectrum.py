"""Integer interval certificates for sparse odd cores in Erdős problem 1052."""

from functools import lru_cache
from fractions import Fraction
from math import gcd, isqrt, prod

from erdos1052_fermat_bases import PATHS, SPLITS, certified_prime, check_valuations, remaining_bases
from erdos1052_group_bounds import SUPPLIERS


@lru_cache(maxsize=200000)
def passes_prime_test(n):
    """Discard only proved composites. Accepting a pseudoprime adds branches."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43):
        if n % p == 0:
            return n == p
    return all(pow(b, n - 1, n) == 1 for b in (2, 3, 5))


@lru_cache(maxsize=50000)
def smooth_mass(bases):
    return prod((Fraction(p, p-1) for p in bases), start=Fraction(1))


@lru_cache(maxsize=150000)
def root_loss(bases, limit):
    """Sum 2/(2^j d) over 2^j d > limit, j>=1, d supported on bases."""
    if not bases:
        return Fraction(4, 1 << max(1, limit.bit_length()))
    p, rest = bases[0], bases[1:]
    power = 1
    total = Fraction()
    while power <= limit:
        total += root_loss(rest, limit // power) / power
        power *= p
    return total + 2*smooth_mass(bases) / power


def next_primes(previous, ceiling, tokens, bases):
    divisors = [(1, 0)]
    for i, q in enumerate(tokens):
        divisors += [(d*q, mask | (1 << i)) for d, mask in divisors
                     if 2*d*q <= ceiling+1]
    shifts = [(d, mask, 1) for d, mask in divisors]
    for p in bases:
        additions = []
        for d, mask, smooth in shifts:
            power = p
            while 2*d*smooth*power <= ceiling+1:
                additions.append((d, mask, smooth*power))
                power *= p
        shifts.extend(additions)
    for d, mask, smooth in shifts:
        odd = d*smooth
        j = max(1, ((previous+1)//odd).bit_length())
        shift = odd << j
        while shift <= ceiling+1:
            q = shift-1
            if (q in (3, 5) or q % 3 == 1) and q not in bases and passes_prime_test(q):
                yield q, d, mask, smooth << j
            shift *= 2
            j += 1


def exclude_interval(low, high, bases=(), required=(3, 5, 7, 19, 223),
                     bit_cap=256, node_cap=200000, sharpen_tail=False):
    """Exclude [low, high) for products of compatible primes with the required members.

    Inconclusive branches (including either resource limit) return None.
    A success gives (nodes, largest ceiling) for the entire finite certificate.
    """
    bases = tuple(sorted(bases))
    required = tuple(sorted(required))
    nodes = 0
    largest = 0

    def visit(previous, tokens, numerator, denominator, missing):
        nonlocal nodes, largest
        nodes += 1
        if nodes > node_cap:
            return False
        if numerator*high.denominator >= high.numerator*denominator:
            return True
        target = low.numerator*denominator
        gap = target - low.denominator*numerator
        if missing:
            ceiling = missing[0]
        elif gap <= 0:
            return False
        else:
            # If the next prime exceeds ceiling, at most len(tokens) paths can
            # cross the prefix. Every other path starts at a smooth shift.
            ceiling = max(previous, (2*len(tokens)+4)*target//gap)
            while (Fraction(2*len(tokens), ceiling+1)
                   + root_loss(bases, ceiling+1)) * target >= gap:
                ceiling = 2*ceiling+1
                if ceiling.bit_length() > bit_cap:
                    return False
        if ceiling.bit_length() > bit_cap:
            return False
        largest = max(largest, ceiling)
        candidates = next_primes(previous, ceiling, tokens, bases)
        if sharpen_tail and not missing:
            far = 8*(ceiling+1)
            # Choose a suffix predecessor whenever one exists. Every suffix
            # path then starts at a shift drawn from the current token set.
            # Starts with nonempty masks use disjoint sets of old tokens.
            scale = 1 << (far.bit_length()+24)
            def rounded(n, d):
                return (n*scale+d-1)//d
            smooth = root_loss(bases, far+1)
            charge = rounded(smooth.numerator, smooth.denominator)
            per_token = [rounded(2, far+1)]*len(tokens)
            charge += sum(per_token)
            choices = []
            for row in sorted(next_primes(previous, far, tokens, bases), reverse=True):
                q, _, mask, _ = row
                bound = rounded(2, q+1)
                if mask:
                    first = (mask & -mask).bit_length()-1
                    charge += max(0, bound-per_token[first])
                    per_token[first] = max(bound, per_token[first])
                else:
                    charge += bound
                if q <= ceiling and charge*target >= gap*scale:
                    choices.append(row)
            candidates = reversed(choices)
        for q, d, mask, factor in candidates:
            new_tokens = tuple(t for i, t in enumerate(tokens) if not (mask >> i) & 1) + (q,)
            new_missing = missing[1:] if missing and q == missing[0] else missing
            if not visit(q, new_tokens, numerator*factor, denominator//d*q, new_missing):
                return False
        return True

    if visit(1, (), 1, 1, required):
        return nodes, largest
    return None


def exponent_bound(factorization, bits=96, **limits):
    """A finite bound a<=bits for a specified nonempty sparse core, or None.

    Supply its factorization as distinct (odd prime, exponent>=2) pairs.
    Exact arithmetic is used for the target. The caller supplies known primes.
    """
    bases = tuple(p for p, _ in factorization)
    if (not bases or len(set(bases)) != len(bases) or any(p <= 2 or e < 2
            for p, e in factorization) or bits < 1):
        raise ValueError("Expected a nonempty odd powerful factorization and positive precision.")
    reciprocal_sum = sum(Fraction(1, p) for p in bases)
    if reciprocal_sum >= Fraction(1, 4096):
        raise ValueError("The sparse-core hypothesis is required.")
    target = 2/prod(1+Fraction(1, p**e) for p, e in factorization)
    patterns = SUPPLIERS[:1] if reciprocal_sum <= Fraction(1, 16384) else SUPPLIERS
    for first, second in patterns:
        if exclude_interval(target-Fraction(1, 1 << bits), target, bases,
                            required=(3, 5, 7, first, second), **limits) is None:
            return None
    return bits


def check(label, low, high, bases=(), required=(3, 5, 7, 19, 223)):
    result = exclude_interval(low, high, bases, required)
    if result is None:
        raise ArithmeticError(f"Inconclusive certificate for {label}")
    print(f"{label}: {result[0]} nodes, largest cutoff {result[1]}")
    return result


def single_base_certificates():
    two = Fraction(2)
    small = Fraction(1, 1 << 38)
    gap = Fraction(1, 1 << 35)
    check("Neutral gap", two-gap, two)
    assert two*(1-small**2)*(1-3*small/(1-small))/(1+Fraction(1, 1 << 64)) > two-gap
    check_valuations()
    assert remaining_bases(1 << 38) == [(167772161, 23)]
    p = 167772161
    gap = Fraction(1, 1 << 40)
    assert two/((1+Fraction(1, p*p))*(1+Fraction(1, 1 << 48))) > two-gap
    check("167772161, all exponents", two-gap, two, (p,))
    p = 65537
    gap = Fraction(1, 1 << 72)
    assert all(p % r == 2 for r in (3, 5, 17, 257))
    assert two/((1+Fraction(1, p**16))*(1+Fraction(1, 1 << 80))) > two-gap
    check("65537, a at least 80", two-gap, two, (p,))
    for a in (16, 48):
        target = Fraction(2 << a, (1 << a)+1)
        assert target/(1+Fraction(1, p**16)) > target-gap
        check(f"65537, a={a}", target-gap, target, (p,))


def two_base_certificates():
    """The complete two-base slices at v2(a)=6 and v2(a)=12."""
    two = Fraction(2)
    large = 67280421310721
    assert 274177*large == (1 << 64)+1 and large % 3 == 2
    assert 274178 == 2*137089 and 137090 == 10*13709 and 13709 % 3 == 2
    assert all(certified_prime(p) for p in (large, 274177, 137089, 13709, 114689, 26017793))
    assert all(p % 3 == 2 and pow(2, 1 << 12, p) == p-1 for p in (114689, 26017793))
    for p, r, threshold in ((274177, large, 2), (137089, large, 5),
                            (13709, large, 5), (114689, 26017793, 3)):
        # None of these pairs contains 65537, so 64 divides a.
        patterns = SUPPLIERS if Fraction(1,p)+Fraction(1,r)>Fraction(1,16384) else SUPPLIERS[:1]
        for e in range(2, threshold+1):
            lower = two/((1+Fraction(1, p**e))*(1+Fraction(1, r*r))*(1+Fraction(1, 1 << 64)))
            upper = two/(1+Fraction(1, p**e)) if e < threshold else two
            for first, second in patterns:
                check(f"{p},{r}, e{'=' if e<threshold else '>='}{e}, suppliers {first},{second}",
                      lower, upper, (p,r), (3,5,7,first,second))


def small_fermat_primes(v, bound):
    """All primes p<=bound equal to 2 mod 3 with p dividing F_v."""
    step = 1 << (v+1)
    first = 1+step*pow(step, -1, 3)
    stride = 3*step
    length = (bound-first)//stride+1
    candidates = bytearray([1])*length
    root = isqrt(bound)
    small_primes = bytearray([1])*(root+1)
    for p in range(2, root+1):
        if not small_primes[p]:
            continue
        if p*p <= root:
            small_primes[p*p::p] = bytes((root-p*p)//p+1)
        if stride % p == 0:
            continue
        start = -first*pow(stride, -1, p) % p
        if first+stride*start == p:
            start += p
        if start < length:
            candidates[start::p] = bytes((length-start-1)//p+1)
    result = []
    index = candidates.find(1)
    while index >= 0:
        p = first+stride*index
        if pow(2, 1 << v, p) == p-1:
            result.append(p)
        index = candidates.find(1, index+1)
    return result


def remaining_two_base_valuations():
    """Exclude every other v between 6 and 19 at exactly two repeated bases."""
    two = Fraction(2)
    power_factor = 1+Fraction(1, 1 << 64)
    for v, (p, r) in SPLITS.items():
        if v == 12:
            continue
        assert certified_prime(p) and certified_prime(r)
        lower = two/((1+Fraction(1, p*p))*(1+Fraction(1, r*r))*power_factor)
        check(f"Two prime factors of F_{v}", lower, two, (p,r))

    for v in (7,8):
        first = PATHS[v][0]
        f = (1 << (1 << v))+1
        second = f//first
        assert f == first*second and certified_prime(first) and certified_prime(second)
        assert second % 3 == 2 and second > 1 << 39
        assert all(certified_prime(p) and p > 1 << 39 for p in PATHS[v] if p > 4096)

    expected = {10: [45592577], 14: [], 16: [], 17: []}
    for v, bits in ((10,38), (14,39), (16,40), (17,39)):
        bound = 1 << bits
        partners = small_fermat_primes(v, bound)
        assert partners == expected[v]
        for p in PATHS[v]:
            if p <= 4096:
                continue
            assert certified_prime(p)
            if p <= 1 << 39:
                # For an arbitrary partner r>bound delete paths using r.
                lower = (two*(1-Fraction(4, bound-1)) /
                         ((1+Fraction(1, p*p))*(1+Fraction(1, bound**2))*power_factor))
                check(f"F_{v}, fixed {p}, partner above 2^{bits}", lower, two, (p,))
            else:
                assert bits >= 39  # Both bases above 2^39 contradict Theorem 1.
            for r in partners:
                lower = two/((1+Fraction(1,p*p))*(1+Fraction(1,r*r))*power_factor)
                check(f"F_{v}, bases {p} and {r}", lower, two, (p,r))
        print(f"F_{v}, required primes through 2^{bits}: {partners}")


def additional_base_exclusions():
    for p, e, bits, cases in ((65537, 16, 78, (16,48,80)), (167772161, 2, 44, (48,))):
        t = Fraction(1, 1 << bits)
        retained = (1-t*t)*(1-4*t/(1-t))
        assert Fraction(1,p)+t < Fraction(1,16384)
        for a in cases:
            target = Fraction(2 << a, (1 << a)+1)
            low = target*retained/(1+Fraction(1,p**e))
            high = Fraction(2) if a == cases[-1] else target
            check(f"{p}, additional reciprocal sum at most 2^-{bits}, a={a} or covered tail",
                  low, high, (p,))
    assert ((1 << 64)+1) % 65537 != 0 and (1 << 64)+1 < 1 << 78


def odd_multiplier_at_sixteen():
    assert all(certified_prime(p) for p in (193,97,7,449,414721,44479210368001,11,71))
    assert pow(2,48,193) == 192 and 194 == 2*97 and 98 == 2*7**2
    assert pow(2,112,449) == 448 and 450 % 9 == 0
    for p, forbidden in ((414721,11), (44479210368001,71)):
        assert pow(2,80,p) == p-1 and (p+1) % forbidden == 0 and forbidden % 3 == 2
    layer = ((1 << 176)+1)//65537
    left = 5304641
    right, residue = divmod(layer, left)
    assert residue == 0 and gcd(left,right) == 1 and left % 3 == right % 3 == 2
    assert gcd(layer,5*65537) == 1


if __name__ == "__main__":
    single_base_certificates()
    two_base_certificates()
    remaining_two_base_valuations()
    additional_base_exclusions()
    odd_multiplier_at_sixteen()
