"""Effective bounds for the variable cyclotomic factor of a sparse core."""

from fractions import Fraction
from itertools import product
from math import gcd, isqrt, prod

from erdos1052_spectrum import exclude_interval, passes_prime_test


def is_prime(n):
    if not passes_prime_test(n):
        return False
    if n < 47:
        return True
    return all(n % d for d in range(3, isqrt(n)+1, 2))


def branching_components(edges):
    """Keep only strongly connected components with multiple internal labels at some vertex."""
    reverse = [[] for _ in edges]
    for vertex, row in enumerate(edges):
        for dest in row:
            if dest >= 0:
                reverse[dest].append(vertex)
    visited = set()
    order = []
    for start in range(len(edges)):
        if start in visited:
            continue
        visited.add(start)
        stack = [(start, iter(edges[start]))]
        while stack:
            vertex, choices = stack[-1]
            for dest in choices:
                if dest >= 0 and dest not in visited:
                    visited.add(dest)
                    stack.append((dest, iter(edges[dest])))
                    break
            else:
                order.append(vertex)
                stack.pop()
    visited.clear()
    result = []
    for start in reversed(order):
        if start in visited:
            continue
        component = [start]
        visited.add(start)
        for vertex in component:
            for source in reverse[vertex]:
                if source not in visited:
                    visited.add(source)
                    component.append(source)
        ids = {v:i for i,v in enumerate(component)}
        rows = [tuple(ids.get(dest,-1) for dest in edges[v]) for v in component]
        if any(sum(dest >= 0 for dest in row) >= 2 for row in rows):
            result.append(rows)
    return result


def modular_chain_certificate(jumps, primes):
    """A zero final count certifies eventual periodicity of every surviving infinite word."""
    groups = [[(0,)*len(jumps)]]
    counts = []
    for p in primes:
        if not is_prime(p) or p <= 2:
            raise ValueError("An odd sieving prime is required.")
        moves = [[(pow(2,j,p)*r-1) % p for j in jumps] for r in range(1,p-1)]
        next_groups = []
        for group in groups:
            edges = [tuple(dest*(p-2)+s-1 if dest >= 0 and 0 < s < p-1 else -1
                           for dest,s in zip(row,step)) for row in group for step in moves]
            next_groups.extend(branching_components(edges))
        groups = next_groups
        counts.append(sum(map(len, groups)))
        if not groups:
            break
    return counts


def floor_log_two(x):
    return (x.numerator // x.denominator).bit_length()-1


SEED_BLOCKS = (
    ((3,5,19,607), (7,223), (31,3967)),
    ((3,5,19,607), (7,223), (31,), (8191,)),
    ((3,5,19), (7,223,1783), (31,991)),
)


def group_windows():
    windows = {}
    for blocks in SEED_BLOCKS:
        weights = [prod(Fraction(q+1,q) for q in block) for block in blocks]
        for mask in product((False,True), repeat=len(blocks)):
            on = tuple(sorted(q for block,take in zip(blocks,mask) if take for q in block))
            off = tuple(sorted(q for block,take in zip(blocks,mask) if not take for q in block))
            low = prod((w for w,take in zip(weights,mask) if take),start=Fraction(1))
            high = 2/prod((w for w,take in zip(weights,mask) if not take),start=Fraction(1))
            windows[on,off] = (low,high)
    return windows


def seed_window_bound(h, D, fixed=None):
    """An unconditional bound on a if the residual D misses the possible windows."""
    if h < 16 or h & (h-1) or D <= 0 or D % 2 == 0:
        raise ValueError("Expected a power of two h >= 16 and a positive odd residual.")
    odd = D*((1 << h)+1)
    k = odd.bit_length()-1
    R = Fraction(odd, 1 << k)
    bound = k
    for (on,off),(low,high) in group_windows().items():
        if fixed is not None and (any(q in fixed for q in on) or any(q not in fixed for q in off)):
            continue
        if low < R <= high:
            return None
        if R > high:
            bound = max(bound, floor_log_two(high/(R-high)))
    return bound


def capped_shift_exponent_bound(h, residual_factors, exceptions, jumps=(1,3),
                                node_cap=None, bit_cap=None):
    """Bound a for an assigned (2^a+1)/(2^h+1) group, or return None on a resource limit.

    residual_factors is the prime factorization of its odd terminal divisor D of c.
    At most exceptions simple primes in this group may have an odd shift valuation
    outside jumps. Use exceptions=None to seek an unconditional certificate.
    The input h is a possible power-of-two part of a. With a finite exception
    count and both resource caps None, this algorithm terminates.
    """
    if h < 16 or h & (h-1) or (exceptions is not None and exceptions < 0):
        raise ValueError("Expected a power of two h >= 16 and a nonnegative exception count.")
    jumps = frozenset(jumps)
    if any(j <= 0 or j % 2 == 0 for j in jumps):
        raise ValueError("The admissible shifts must be positive and odd.")
    for r in (1,3):
        part = {j for j in jumps if j % 4 == r}
        if len(part) > 1 and part not in ({3,7}, {1,9}):
            raise ValueError("This shift alphabet needs another recurrence certificate.")
    factors = tuple(sorted(residual_factors))
    if (len({p for p,_ in factors}) != len(factors)
            or any(e < 1 or p <= 2 or not is_prime(p) for p,e in factors)):
        raise ValueError("Expected distinct odd prime factors with positive exponents.")
    D = prod(p**e for p,e in factors)
    odd = D*((1 << h)+1)
    k = odd.bit_length()-1
    target = Fraction(odd, 1 << k)
    bound = k  # The unique normalized target is assured once a>k.
    stack = [(1, factors, Fraction(1), exceptions)]
    nodes = 0
    while stack:
        previous, supply, partial, left = stack.pop()
        nodes += 1
        if node_cap is not None and nodes > node_cap:
            return None
        if partial >= target:
            continue
        gap = target-partial
        bound = max(bound, floor_log_two(2*target/gap))
        count = sum(e for _,e in supply)
        # With no next prime through this ceiling, the entire remaining
        # product, including partial, is at most (target+partial)/2.
        limit = (2*count+4)*(target+partial)/gap
        ceiling = limit.numerator // limit.denominator + 1
        if bit_cap is not None and ceiling.bit_length() > bit_cap:
            return None
        for uses in product(*(range(e+1) for _,e in supply)):
            d = prod(p**u for (p,_),u in zip(supply,uses))
            j = max(1, ((previous+1)//d).bit_length())
            shift = d << j
            while shift <= ceiling+1:
                q = shift-1
                cost = int(j % 2 == 1 and j not in jumps)
                if ((left is None or cost <= left) and (q in (3,5) or q % 3 == 1)
                        and gcd(q,D)==1 and is_prime(q)):
                    rest = tuple((p,e-u) for (p,e),u in zip(supply,uses) if e>u)
                    available = None if left is None else left-cost
                    stack.append((q, rest+((q,1),), partial*Fraction(q+1,q), available))
                j += 1
                shift *= 2
    return bound, nodes


def small_terminal_certificate(limit=1 << 24):
    """Exclude all nontrivial prime-power layers with terminal D <= 2^24."""
    if not 4097 <= limit <= 1 << 24:
        raise ValueError("The prime-only argument applies through 2^24.")
    prime = bytearray([1])*(limit+1)
    prime[:2] = bytes(2)
    for p in range(2,isqrt(limit)+1):
        if prime[p]:
            prime[p*p::p] = bytes((limit-p*p)//p+1)
    windows = group_windows()
    primes = checks = nodes = 0
    for p in range(4097,limit+1):
        if not prime[p]:
            continue
        primes += 1
        m = p*65537
        R = Fraction(m, 1 << (m.bit_length()-1))
        T = Fraction(p, 1 << (p.bit_length()-1))
        for low,high in ((R/(1+Fraction(1,1 << 80)),R),
                         (T,T*(1+Fraction(1,1 << 64)))):
            for (on,off),(bottom,top) in windows.items():
                if low >= top or high <= bottom:
                    continue
                checks += 1
                result = exclude_interval(max(bottom,low), min(top,high), (p,), on,
                                          bit_cap=240, node_cap=300000, sharpen_tail=True,
                                          forbidden=off, multiplicities={p:1})
                if result is None:
                    raise ArithmeticError(f"Unresolved at {p}, {low}, {on}, {off}")
                nodes += result[0]
    return primes, checks, nodes


def mersenne_terminal_certificates():
    """The remaining finite case of the unrestricted Mersenne-terminal theorem."""
    assert ((1 << 29)-1) % 233 == 0
    p = (1 << 31)-1
    T = Fraction(p, 1 << 30)
    counts = []
    for (on,off),(bottom,top) in group_windows().items():
        low,high = max(T,bottom),min(T*(1+Fraction(1,1 << 64)),top)
        if low < high:
            result = exclude_interval(low,high,(p,),on,sharpen_tail=True,forbidden=off,
                                      multiplicities={p:1})
            assert result is not None
            counts.append(result[0])
    assert sorted(counts) == [18,83,90]


if __name__ == "__main__":
    assert modular_chain_certificate((3,7), (7,11,13,17,19)) == [4,18,112,221,0]
    assert modular_chain_certificate((1,9), (7,11,13,17,19,23,29,31,37)) == [
        4,26,87,783,5445,576,576,9099,0]
    assert seed_window_bound(16,13709) == 29
    mersenne_terminal_certificates()
    for p in (5003, 65537, 13709, 114689, 167772161):
        print(p, capped_shift_exponent_bound(16, ((p,1),), None, node_cap=10000,
                                             bit_cap=48), flush=True)
    print("Terminal bound through 2^24 (primes, intervals, nodes)",
          small_terminal_certificate(), flush=True)
