"""Exact exclusions for Erdős 1052, with no cutoff on n or the exponent of 2.

The companion mathematical argument is in Erdős1052-core-bounds.txt.
All interval decisions use Fraction. A failed certificate leaves the case open.
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import isqrt, prod

from search_1052 import factor, odd_powerful_numbers


def forced(core, seed_divisor=1):
    """Cancel all odd factors already supplied by the seed divisor and the core."""
    bases = dict(factor(core))
    demands = Counter(dict(factor(seed_divisor)))
    for p, e in bases.items():
        demands.update(dict(factor(p ** e + 1)))
    demands.pop(2, None)
    fixed = set()
    remaining = core
    while demands:
        p = max(demands)
        count = demands.pop(p)
        if p in bases:
            if remaining % (p ** count):
                return None
            remaining //= p ** count
        else:
            if count != 1:
                return None
            fixed.add(p)
            demands.update({q: e for q, e in factor(p + 1) if q != 2})
    sigma_core = prod(p ** e + 1 for p, e in bases.items())
    ratio = Fraction(sigma_core * prod(p + 1 for p in fixed), core * prod(fixed))
    assert ratio.denominator == remaining * seed_divisor
    assert ratio.numerator & (ratio.numerator - 1) == 0
    return frozenset(fixed), remaining, ratio


@lru_cache(maxsize=None)
def primes_through(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytes((n - p * p) // p + 1)
    return tuple(p for p in range(3, n + 1, 2) if sieve[p])


@lru_cache(maxsize=None)
def mersenne_tail(x):
    # For k >= 31, sum 2^(1-k) = 2^-29. The reciprocal product is
    # at most 2^29/(2^29-1). Factor the smaller prime exponents exactly.
    start = max(31, (x + 1).bit_length())
    denominator = 2 ** (start - 2)
    result = Fraction(denominator, denominator - 1)
    for k in (2,) + primes_through(30):
        p = 2 ** k - 1
        if p > x and factor(p) == ((p, 1),):
            result *= Fraction(p + 1, p - 1)
    return result


@lru_cache(maxsize=None)
def tail_bound(x, count):
    return (1 + Fraction(2, x)) ** count * mersenne_tail(x)


@lru_cache(maxsize=None)
def single_base_roots(p):
    """Additional starts with q+1 = 2^j p^s, s>0, through 2^35."""
    limit = (1 << 35)+1
    roots = []
    power = p
    while power <= limit:
        shift = 2*power
        while shift <= limit:
            q = shift-1
            if factor(q) == ((q, 1),):
                roots.append(q)
            shift *= 2
        power *= p
    return tuple(sorted(roots))


@lru_cache(maxsize=None)
def single_base_tail(x, p):
    """Bound the product of additional root path factors above x."""
    limit = max((1 << 35)+1, x+1)
    loss = sum((Fraction(2, q+1) for q in single_base_roots(p) if q > x), Fraction())
    power = 1
    while power <= limit//p:
        power *= p
        shift = 2*power
        while shift <= limit:
            shift *= 2
        loss += Fraction(4, shift)  # geometric tail over the powers of two
    loss += Fraction(2, power*(p-1))  # all remaining powers of p
    return 1/(1-loss)


def possible_next_primes(x, y, tokens, free_prime=None):
    """List all candidate shifts, optionally removing one prime base from their odd parts."""
    divisors = [1]
    for p, e in tokens:
        powers = [p ** i for i in range(1, e + 1)]
        divisors.extend([d * power for d in divisors for power in powers if 2 * d * power <= y + 1])
    candidates = []
    for d in divisors:
        start = 2*d
        while start-1 <= y:
            v = start
            while v-1 <= y:
                q = v-1
                if q > x and q != free_prime and factor(q) == ((q, 1),):
                    candidates.append((q, d))
                v *= 2
            if free_prime is None:
                break
            start *= free_prime
    return sorted(candidates)


def uniform_gap(core, seed_divisor, target, max_prime=4096, upper=None, allowed=None,
                required=(), two_budget=None, free_prime=None):
    """Exclude the interval [target, upper) of compatible odd abundancies.

    max_prime limits the certificate search. The tail lemma covers all larger
    primes at every successful leaf. None indicates an inconclusive search.
    With upper=None the certificate proves a strict upper bound. If some
    primes are required, a continuation cannot skip its least missing one.
    two_budget bounds the sum of v2(q+1) over the additional simple primes.
    With core=seed_divisor=1, free_prime=p permits unlimited copies of
    the repeated prime p>3 in the shifted factors of the simple primes.
    """
    if free_prime is not None and ((core, seed_divisor) != (1, 1) or free_prime <= 3
                                   or factor(free_prime) != ((free_prime, 1),)):
        raise ValueError("A free prime requires an unseeded group and a prime base greater than 3.")
    state = forced(core, seed_divisor)
    if state is None:
        return 0, 0
    fixed, initial_tokens, initial_ratio = state
    forbidden = fixed | set(dict(factor(core)))
    pending = tuple(sorted(set(required) - fixed))
    if any(q in forbidden or (allowed is not None and not allowed(q)) for q in pending):
        return 0, 0
    nodes = 0
    max_cut = 0

    def visit(x, tokens, count, ratio, needed, budget):
        nonlocal nodes, max_cut
        nodes += 1
        if upper is not None and ratio >= upper:
            return True

        def tail(y):
            bound = tail_bound(y, count)
            if free_prime is not None:
                bound *= single_base_tail(y, free_prime)
            if budget is not None:
                bound = min(bound, (1+Fraction(1, y+1))**budget)
            return bound

        y = min(max_prime, needed[0]) if needed else max_prime
        if ratio * tail(y) < target:
            # All continuations whose next prime exceeds this cutoff fall below target.
            low, high = x - 1, y
            while high - low > 1:
                mid = (low + high) // 2
                if ratio * tail(mid) < target:
                    high = mid
                else:
                    low = mid
            y = high
        elif not needed or needed[0] > y:
            return False
        max_cut = max(max_cut, y)
        for p, odd in possible_next_primes(x, y, tokens, free_prime):
            if p in forbidden or (allowed is not None and not allowed(p)):
                continue
            remaining_budget = budget
            if budget is not None:
                remaining_budget -= ((p+1) & -(p+1)).bit_length()-1
                if remaining_budget < 0:
                    continue
            use = dict(factor(odd))
            remaining = tuple((q, e - use.get(q, 0)) for q, e in tokens if e > use.get(q, 0))
            next_count = count + 1 - sum(use.values())
            left = needed[1:] if needed and p == needed[0] else needed
            if not visit(p, remaining + ((p, 1),), next_count, ratio * Fraction(p + 1, p),
                         left, remaining_budget):
                return False
        return True

    count = sum(e for _, e in factor(initial_tokens))
    return ((nodes, max_cut) if visit(1, factor(initial_tokens), count, initial_ratio,
                                     pending, two_budget) else None)


def known_multiple_certificate():
    """Extra odd-prime paths cannot supply the needed ratio for a=18j, odd j>1."""
    fixed, tokens, ratio = forced(625, 2 ** 18 + 1)
    assert tokens == 1 and ratio == Fraction(2 ** 19, 2 ** 18 + 1)
    n = 2 ** 18 * 625 * prod(fixed)
    assert n == 146361946186458562560000
    assert ratio * (1 + Fraction(1, 2 ** 18)) == 2
    p = 2 ** 19 - 1
    small_roots = [2 ** k - 1 for k in primes_through(30)
                   if 2 ** 18 < 2 ** k - 1 and factor(2 ** k - 1) == ((2 ** k - 1, 1),)]
    assert small_roots == [p]
    q = 2 * p - 1
    assert (2 * q - 1) % 5 == 0 and 2 * q - 1 > 5

    def w(r):
        return Fraction(r + 1, r - 1)

    first = 1 + Fraction(1, p)
    slow = first * w(4 * p - 1)
    fast = first * (1 + Fraction(1, q)) * w(4 * q - 1)
    bound = max(slow, fast) * Fraction(2 ** 29, 2 ** 29 - 1)
    required = (1 + Fraction(1, 2 ** 18)) / (1 + Fraction(1, 2 ** 54))
    assert bound < required
    return n


def single_large_prime_power():
    """Numerical inequalities for the uniform theorem about c=p^e, p>65537."""
    P = 65537
    correction = (1 + Fraction(1, P ** 2)) / (1 - Fraction(3, P - 1))
    for a in range(1, 20):
        lowbit = a & -a
        m = 2 ** lowbit + 1
        target = 2 / (1 + Fraction(1, 2 ** a))
        assert uniform_gap(1, m, target / correction, upper=target) is not None
    target = Fraction(1024, 513)
    for m in (3, 5, 17, 257, 65537, 641):
        assert uniform_gap(1, m, target, upper=2) is not None
    assert (2 ** 32 + 1) % 641 == 0
    assert target * correction * (1 + Fraction(1, 1024)) * (1 + Fraction(1, 2 ** 20)) < 2


def unique_prime_above_three():
    """Bound the prime that supplies the single factor 3 when c=625 and a>=20."""
    frequency = 1 + Fraction(1, 2 ** 20)
    assert uniform_gap(625, 5, 2 / frequency, upper=2, allowed=lambda q: q % 3 == 1) is not None
    bound = 176
    threshold = 2 / (frequency * Fraction(bound + 1, bound - 1))
    assert uniform_gap(625, 15, threshold, max_prime=16384, upper=2) is not None
    candidates = []
    for p in primes_through(bound - 1):
        if p % 3 != 2 or p == 5 or forced(625, 5 * p) is None:
            continue
        # Proper ancestors of p, if present, start at a prime at least 2p-1.
        first_parent = 2 * p - 1
        threshold = 2 / (frequency * Fraction(first_parent + 1, first_parent - 1))
        if uniform_gap(625, 5 * p, threshold, max_prime=16384, upper=2) is None:
            candidates.append(p)
    return candidates


def direct_small(core, amin, amax):
    from search_1052 import squarefree_completion
    bases = dict(factor(core))
    result = []
    for a in range(amin, amax + 1):
        seed = 1 if a == 0 else 2 ** a + 1
        balance = Counter(dict(factor(seed)))
        balance[2] -= a + 1
        for p, e in bases.items():
            balance.update(dict(factor(p ** e + 1)))
            balance[p] -= e
        if squarefree_completion(balance, bases) is not None:
            result.append(a)
    return result


@lru_cache(maxsize=None)
def may_divide_seed_at_64(p):
    # Fermat's little theorem makes this a complete residue test for p.
    return any(pow(2, 64 * k, p) == p - 1 for k in range(p - 1))


def classify_bounded_cores(limit):
    # If a >= 20 the odd abundancy must be in [target, 2).
    target = Fraction(2 ** 21, 2 ** 20 + 1)
    ceiling = 2 ** 24
    causes = Counter()
    unresolved = []
    small_solutions = []
    assert not any(may_divide_seed_at_64(p) for p in primes_through(1024) if p % 3 == 2)
    for c in sorted(odd_powerful_numbers(limit)):
        state = forced(c)
        if state is None:
            causes["divisibility"] += 1
            continue
        # Check a=0 here too, since the factor contributed by 2 is then 1.
        small_solutions.extend((a, c) for a in direct_small(c, 0, 19))
        if state[2] >= 2:
            causes["abundancy"] += 1
            continue
        if uniform_gap(c, 1, target, max_prime=ceiling, upper=2) is not None:
            causes["unseeded interval"] += 1
            continue
        # v_2(a)=0,...,5. If a/2^v is odd, 2^(2^v)+1 divides 2^a+1.
        seeds = [2 ** (2 ** v) + 1 for v in range(6)]
        if any(uniform_gap(c, m, target, max_prime=ceiling, upper=2) is None for m in seeds):
            unresolved.append(c)
            continue
        # If 64|a, remove a seed prime p = 2 mod 3. Its successor sum
        # p+1 supplies the artificial seed divisor 3 in the remaining support.
        if (any(p % 3 == 2 and may_divide_seed_at_64(p) for p, _ in factor(c))
                or uniform_gap(c, 3, Fraction(1024, 513), max_prime=ceiling, upper=2) is None):
            unresolved.append(c)
            continue
        causes["exponent classes"] += 1
    return causes, unresolved, small_solutions


def run():
    # Each successful interval check is valid for arbitrarily large exponents.
    for c in (27, 81, 225, 343, 1089, 2401):
        passed = uniform_gap(c, 1, Fraction(64, 33))
        assert passed is not None and direct_small(c, 0, 4) == []
        print(f"c={c}: no exponent; {passed[0]} nodes, largest cutoff {passed[1]}")
    gap = Fraction(1024, 513)
    passed = uniform_gap(625, 3, gap)
    assert passed is not None and direct_small(625, 0, 8) == []
    print(f"c=625, reserve 3: odd abundancy < {gap}; {passed[0]} nodes, cutoff {passed[1]}")
    for v in range(2, 6):
        seed = 2 ** (2 ** v) + 1
        assert forced(625, seed) is None
    # If 64 divides a, a seed prime congruent to 2 modulo 3 must exceed 1024.
    # The multiplicative order of 2 modulo p divides p-1.
    assert not any(may_divide_seed_at_64(p) for p in primes_through(1024) if p % 3 == 2)
    assert (1 + Fraction(1, 1024)) * (1 + Fraction(1, 2 ** 64)) < Fraction(513, 512)
    print("c=625: no odd exponent or exponent divisible by 4")
    assert uniform_gap(625, 2 ** 10 + 1, Fraction(2 ** 11, 2 ** 10 + 1)) is not None
    for t in (7, 11, 13, 17, 19, 23, 29, 31):
        assert forced(625, 2 ** (2 * t) + 1) is None
    assert forced(625, 2 ** 54 + 1) is None
    n = known_multiple_certificate()
    print(f"c=625: the unique solution with 18 dividing a is a=18, n={n}")
    print("c=625: writing a=2k, k must be coprime to 5,7,11,13,17,19,23,29,31")
    print(f"c=625, a>=20: unique simple prime equal to 2 mod 3 lies in {unique_prime_above_three()}")
    single_large_prime_power()
    print("c=p^e, p>65537: 64 divides a, e is even, and p is the unique prime 2 mod 3 dividing F_v, v=v_2(a)")
    counts, unresolved, small = classify_bounded_cores(100_000_000)
    assert small == [(1, 1), (2, 1), (6, 1), (1, 9), (18, 625)]
    print(f"c <= 10^8, a <= 19: {small} (a,c)")
    print(f"c <= 10^8, a >= 20: {dict(counts)}, {len(unresolved)} unresolved")
    print("Remaining cores:", ", ".join(map(str, unresolved)))


if __name__ == "__main__":
    run()
