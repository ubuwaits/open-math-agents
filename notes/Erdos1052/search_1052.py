"""Search Erdős 1052 by fixing the 2-adic exponent and the repeated odd prime powers.

Run with Python 3.9 or later. Each bound is inclusive. There is no bound on
the squarefree part of n or on n itself. Trial division uses integer arithmetic.
"""

import argparse
from collections import Counter
from functools import lru_cache
from math import isqrt, prod


@lru_cache(maxsize=None)
def factor(n):
    """Return the prime factorization of a positive integer."""
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            exponent = 0
            while n % p == 0:
                n //= p
                exponent += 1
            result.append((p, exponent))
        p = 3 if p == 2 else p + 2
    if n > 1:
        result.append((n, 1))
    return tuple(result)


def odd_powerful_numbers(limit):
    """Every powerful number is uniquely x^2 y^3 with y squarefree."""
    y = 1
    while y ** 3 <= limit:
        if all(e == 1 for _, e in factor(y)):
            for x in range(1, isqrt(limit // y ** 3) + 1, 2):
                yield x * x * y ** 3
        y += 2


def squarefree_completion(balance, forbidden):
    """Recover the distinct odd primes from denominator-minus-numerator valuations."""
    balance = balance.copy()
    support = []
    while True:
        p = max((q for q, e in balance.items() if q != 2 and e), default=0)
        if p == 0:
            return tuple(support) if balance[2] == 0 else None
        if balance[p] != 1 or p in forbidden:
            return None
        support.append(p)
        del balance[p]
        # Dividing the requested ratio by (p+1)/p introduces only smaller odd primes.
        balance.update(dict(factor(p + 1)))


def search(max_core, max_exponent):
    seeds = []
    for a in range(max_exponent + 1):
        sigma_two_part = 1 if a == 0 else 2 ** a + 1
        balance = Counter(dict(factor(sigma_two_part)))
        balance[2] -= a + 1
        seeds.append(balance)

    results = []
    cores = 0
    for core in odd_powerful_numbers(max_core):
        cores += 1
        components = dict(factor(core))
        odd_balance = Counter()
        for p, e in components.items():
            odd_balance.update(dict(factor(p ** e + 1)))
            odd_balance[p] -= e
        for a, seed in enumerate(seeds):
            balance = seed.copy()
            balance.update(odd_balance)
            support = squarefree_completion(balance, components)
            if support is None:
                continue
            n = (2 ** a) * core * prod(support)
            sigma = 1 if a == 0 else 2 ** a + 1
            sigma *= prod(p ** e + 1 for p, e in components.items())
            sigma *= prod(p + 1 for p in support)
            assert sigma == 2 * n
            results.append((n, a, core, support))
    return cores, sorted(results)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-core", type=int, default=100_000_000)
    parser.add_argument("--max-exponent", type=int, default=48)
    args = parser.parse_args()
    if args.max_core < 1 or args.max_exponent < 0:
        parser.error("max-core must be positive and max-exponent must be nonnegative")
    cores, results = search(args.max_core, args.max_exponent)
    print(f"{cores:,} odd powerful cores, {cores * (args.max_exponent + 1):,} parameter pairs")
    for n, a, core, support in results:
        print(f"n = {n}, a = {a}, c = {core}, remaining primes = {support}")
