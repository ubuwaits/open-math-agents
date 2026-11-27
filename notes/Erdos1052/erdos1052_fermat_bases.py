"""Exact exclusions for unitary perfect numbers with one sparse repeated prime.

The proof is in section 11 of Erdős1052-large-prime-branches.txt. All the
input numbers below are verified with integer arithmetic. No network or
external number-theory package is needed to reproduce the certificates.
"""

from functools import lru_cache
from math import gcd, isqrt, prod


# Two coprime divisors of the same Fermat number, each 2 modulo 3.
SPLITS = {
    9: (2424833, 7455602825647884208337395736200454918783366342657),
    11: (974849, 3560841906445833920513),
    12: (114689, 26017793),
    13: (2710954639361, 2663848877152141313),
    15: (2327042503868417, 168768817029516972383024127016961),
    18: (13631489, 81274690703860512587777),
    19: (70525124609, 37590055514133754286524446080499713),
}

# Each entry before the last is a prime equal to 1 modulo 3. The last
# entry is 2 modulo 3 and coprime to both 5 and the Fermat number.
PATHS = {
    6: (274177, 137089, 13709),
    7: (5704689200685129054721, 407477800048937789623, 59),
    8: (93461639715357977769163558199606896584051237541638188580280321,
        6813678835133),
    10: (6487031809, 92671883),
    14: (116928085873074369829035993834596371340386703423373313,
         9661881871, 603867617),
    16: (825753601, 113),
    17: (31065037602817, 67, 17),
}

EXCLUDED_SINGLE_PRIME_VALUATIONS = frozenset(SPLITS) | frozenset(PATHS)

# For 167772161^e, these are forced by the shift when ν₂(e) is the key.
# The last odd factor is 2 modulo 3, with no prime factor 5 or 167772161.
CORE_SHIFT_PATHS = {
    0: (3,),
    1: (14073749003304961, 7036874501652481, 911),
    2: (41,), 3: (17,), 4: (1601,), 6: (257,), 8: (26113, 11),
    10: (59393,), 15: (65537,),
}


def can_absorb_path(bases, chain):
    """A forced chain must end at a repeated prime before using a forbidden simple prime."""
    return (any(r in bases for r in chain[:-1]) or
            any(p % 3 == 2 and chain[-1] % p == 0 for p in bases))


def allows_valuation(bases, v):
    if v in PATHS:
        return can_absorb_path(bases, PATHS[v])
    if v in SPLITS:
        return all(any(p % 3 == 2 and d % p == 0 for p in bases) for d in SPLITS[v])
    return True

# Complete factorizations of n−1 for Lucas primality certificates.
LUCAS_FACTORS = {
    # Additional Lucas certificates for the two-base Fermat-number exclusions.
    1143290228161321: ((2, 3), (3, 2), (5, 1), (29, 1), (101, 1), (1084262953, 1)),
    514601075709020317: ((2, 2), (3, 1), (594163, 1), (72174509311, 1)),
    43226490359557706629: ((2, 2), (3, 1), (7, 1), (514601075709020317, 1)),
    7455602825647884208337395736200454918783366342657: ((2, 11), (19, 1), (47, 1), (82488781, 1), (1143290228161321, 1), (43226490359557706629, 1)),
    91722533083549: ((2, 2), (3, 1), (2021081, 1), (3781909, 1)),
    3560841906445833920513: ((2, 13), (7, 1), (677, 1), (91722533083549, 1)),
    2710954639361: ((2, 16), (5, 1), (11, 1), (752107, 1)),
    1069660739759: ((2, 1), (13, 1), (73, 1), (563, 1), (1001017, 1)),
    2663848877152141313: ((2, 17), (19, 1), (1069660739759, 1)),
    2327042503868417: ((2, 17), (14431, 1), (1230263, 1)),
    168768817029516972383024127016961: ((2, 17), (5, 1), (7, 1), (53, 1), (97, 1), (181, 1), (199, 1), (1331471, 1), (149211834097, 1)),
    81274690703860512587777: ((2, 23), (29, 1), (293, 1), (1259, 1), (905678539, 1)),
    69290733008201: ((2, 3), (5, 2), (11, 1), (73, 1), (1523, 1), (283289, 1)),
    8962167624028624126082526703: ((2, 1), (3, 1), (67, 1), (389, 1), (1609, 1), (514051, 1), (69290733008201, 1)),
    37590055514133754286524446080499713: ((2, 22), (8962167624028624126082526703, 1)),
    116503103764643: ((2, 1), (7, 1), (449, 1), (18533742247, 1)),
    59649589127497217: ((2, 9), (116503103764643, 1)),
    1238926361552897: ((2, 11), (157, 1), (3853149761, 1)),
    14073749003304961: ((2, 25), (3, 1), (5, 1), (27962027, 1)),
    7036874501652481: ((2, 24), (3, 1), (5, 1), (27962027, 1)),
    5704689200685129054721: ((2, 9), (3, 5), (5, 1), (12497, 1), (733803839347, 1)),
    407477800048937789623: ((2, 1), (3, 1), (11, 1), (19, 1), (324942424281449593, 1)),
    324942424281449593: ((2, 3), (3, 1), (17, 1), (509, 1), (933019, 1), (1677019, 1)),
    93461639715357977769163558199606896584051237541638188580280321:
        ((2, 11), (3, 1), (5, 1), (7, 1), (13, 1), (31618624099079, 1),
         (1057372046781162536274034354686893329625329, 1)),
    1057372046781162536274034354686893329625329:
        ((2, 4), (3, 1), (8861, 1), (10608557, 1), (25353082741699, 1), (9243081088796207, 1)),
    9243081088796207: ((2, 1), (20939, 1), (220714482277, 1)),
    116928085873074369829035993834596371340386703423373313:
        ((2, 16), (3, 3), (9959563, 1), (761145015334071629, 1), (8717008205877092841673, 1)),
    761145015334071629: ((2, 2), (13, 1), (1439, 1), (3463, 1), (2937316727, 1)),
    8717008205877092841673: ((2, 3), (3, 2), (188107, 1), (643620696810643, 1)),
    643620696810643: ((2, 1), (3, 2), (127, 1), (50153, 1), (5613799, 1)),
}


@lru_cache(maxsize=None)
def certified_prime(n):
    factors = LUCAS_FACTORS.get(n)
    if factors is None:
        assert n <= 10**14, 'A Lucas certificate is needed for this entry.'
        return n == 2 or (n > 2 and n % 2 == 1 and all(n % d for d in range(3, isqrt(n)+1, 2)))
    assert prod(q**k for q, k in factors) == n-1
    assert all(certified_prime(q) for q, _ in factors)
    # The multiplicative order of a successful witness modulo n is n−1.
    # Euler's theorem then gives φ(n)≥n−1, which forces n to be prime.
    return any(pow(g, n-1, n) == 1 and all(pow(g, (n-1)//q, n) != 1 for q, _ in factors)
               for g in range(2, 1000))


def check_valuations():
    assert EXCLUDED_SINGLE_PRIME_VALUATIONS == frozenset(range(6, 20))
    for v, (left, right) in SPLITS.items():
        assert left % 3 == right % 3 == 2 and gcd(left, right) == 1
        assert all(pow(2, 1 << v, f) == f-1 for f in (left, right))
    for v, chain in PATHS.items():
        assert pow(2, 1 << v, chain[0]) == chain[0]-1
        for p, d in zip(chain, chain[1:]):
            assert certified_prime(p) and p % 3 == 1 and (p+1) % d == 0
        d = chain[-1]
        assert d % 3 == 2 and gcd(d, 5) == gcd(d, pow(2, 1 << v, d)+1) == 1
    p = 167772161
    assert certified_prime(p) and pow(2, 1 << 23, p) == p-1
    for j, chain in CORE_SHIFT_PATHS.items():
        assert pow(p, 1 << j, chain[0]) == chain[0]-1
        for r, d in zip(chain, chain[1:]):
            assert certified_prime(r) and r != p and (r+1) % d == 0
        d = chain[-1]
        if d == 3:
            assert j == 0  # 5+1 already supplies the unique copy of 3.
        else:
            assert d % 3 == 2 and gcd(d, 5*p) == 1


def remaining_bases(limit):
    possible = []
    for v in range(20, limit.bit_length()):
        order = 1 << (v+1)
        for p in range(order+1, limit+1, order):
            if p % 3 == 2 and pow(2, 1 << v, p) == p-1:
                possible.append((p, v))
    return sorted(possible)


if __name__ == '__main__':
    check_valuations()
    assert remaining_bases(10**12) == [(167772161, 23)]
    print('Verified all 14 valuation exclusions and all nine shift exclusions for '
          '167772161. Through 10^12 the only candidate sparse prime-power bases '
          'are 65537 and 167772161.')
