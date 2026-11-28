"""Effective bounds for the variable cyclotomic factor of a sparse core."""

from fractions import Fraction
from itertools import combinations, product
from math import gcd, isqrt, prod

from erdos1052_fermat_bases import certified_prime
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


def normalized_residual_windows(all_scales=False):
    """Merge the necessary intervals in one octave. Width is logarithmic."""
    spread = 1+Fraction(1,65536) if all_scales else Fraction(1)
    intervals = []
    for low,high in group_windows().values():
        low /= spread
        if low < 1:
            intervals.append((2*low,Fraction(2)))
            low = Fraction(1)
        intervals.append((low,high))
    merged = []
    for low,high in sorted(intervals):
        if merged and low <= merged[-1][1]:
            merged[-1] = (merged[-1][0],max(merged[-1][1],high))
        else:
            merged.append((low,high))
    return tuple(merged)


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


def dyadic_root_bound(h, residual_factors):
    """Bound a at a specified sparse core using only the possible path starts.

    residual_factors is the prime factorization of the residual at h.
    None means the loss inequality gives no bound.
    """
    if h < 16 or h & (h-1):
        raise ValueError("Expected a power of two h >= 16.")
    factors = tuple(residual_factors)
    if any(p <= 4096 or p % 3 == 0 or e < 1 for p,e in factors):
        raise ValueError("Expected the prime-power factors of a sparse residual.")
    D = prod(p**e for p,e in factors)
    target = ((1 << h)+1)*D
    k = target.bit_length()-1
    R = Fraction(target,1 << k)
    loss = 1-1/R
    s = floor_log_two(1/loss)
    if s < 3:
        return None

    # The two finite divisor products count roots with even and odd jumps.
    sums = []
    for twisted in (False,True):
        total = Fraction(1)
        for p,e in factors:
            sign = -1 if twisted and p % 3 == 2 else 1
            x = Fraction(sign,p)
            total *= (1-x**(e+1))/(1-x)
        sums.append(total)
    core_loss = sums[0]+sums[1]/3-Fraction(4,3)

    # Only odd prime exponents can start a Mersenne path above the cutoff.
    first = s+1 if s % 2 == 0 else s+2
    stop = first+24
    mersenne_loss = Fraction(4,3)*Fraction(2,1 << stop)
    for j in range(first,stop,2):
        if is_prime(j) and all(p != (1 << j)-1 for p,_ in factors):
            mersenne_loss += Fraction(2,1 << j)
    gap = loss-core_loss-mersenne_loss
    return max(k, floor_log_two(1/(R*gap))) if gap > 0 else None


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


def three_base_gap_certificate():
    """Bound the reciprocal mass outside 65537, 2^31-1 and 2^61-1."""
    p,r,s = 65537,(1 << 31)-1,(1 << 61)-1
    t = Fraction(1,1 << 76)
    keep = (1-4*t)*(1-t*t)
    correction = prod(1+Fraction(1,q**e) for q,e in ((2,80),(p,16),(r,3),(s,2)))
    width = Fraction(1,1 << 72)
    assert 2*keep/correction > 2-width
    counts = []
    for m in range(4):
        for bases in combinations((p,r,s),m):
            targets = [Fraction(2)]
            if r in bases:
                targets.append(2/(1+Fraction(1,r*r)))
            for target in targets:
                for blocks in SEED_BLOCKS:
                    required = sorted(q for block in blocks for q in block)
                    result = exclude_interval(target-width,target,bases,required,
                                              sharpen_tail=True)
                    if result is None:
                        raise ArithmeticError(f"Unresolved at {bases}, {target}, {required}")
                    counts.append(result[0])
    proper_divisors = ((23,47),(29,233),(37,223),(41,13367),(43,431),
                       (47,2351),(53,6361),(59,179951),(67,193707721),
                       (71,228479),(73,439))
    assert all(1<d<(1 << k)-1 and pow(2,k,d)==1 for k,d in proper_divisors)
    assert {k for k in range(13,79) if is_prime(k)} == (
        {13,17,19,31,61} | {k for k,_ in proper_divisors})
    return len(counts),sum(counts)


def six_base_gap_certificate():
    """Verify the small-exponent obstructions and all forbidden core/block configurations."""
    bases = (8191, 65537, 131071, 524287, (1 << 31)-1, (1 << 61)-1)
    min_exponents = (8, 16, 7, 7, 4, 3)
    cases = {8191: ((2,41), (3,193), (5,11), (6,41), (7,29)),
             131071: ((2,13), (3,7), (4,2801), (5,11), (6,13)),
             524287: ((2,5), (3,13), (4,89), (5,491), (6,5)),
             (1 << 31)-1: ((2,5), (3,13)),
             (1 << 61)-1: ((2,3389),)}
    for p, pairs in cases.items():
        for exponent, q in pairs:
            assert certified_prime(q) and pow(p, exponent, q) == q-1
            assert q in (5,7,13,193) or (q < 4096 and q % 3 == 2)
    assert (193+1) % 97 == 0 and (97+1) % 49 == 0 and certified_prime(97)
    for j, q in enumerate((3,5,17,257)):
        assert pow(65537, 1 << j, q) == q-1 and certified_prime(q)

    # The fourth power at 8191 forces two ordinary primes, the second spending 5.
    q, r = 2250700503367681, 59228960614939
    factors = (2,3,5,7,13,41,101,8101)
    assert q-1 == 2**14*3**2*5*7*13*41*101*8101
    assert all(certified_prime(d) for d in factors)
    assert pow(19,q-1,q) == 1 and all(pow(19,(q-1)//d,q) != 1 for d in factors)
    assert certified_prime(r) and (8191**4+1) == 2*q and q+1 == 38*r
    assert (r+1) % 5 == 0 and q not in bases and r not in bases and q < 1 << 76

    # With no further core base below 2^76, these divisors rule out all a<256.
    for h, divisor in ((64,67280421310721), (128,59649589127497217),
                       (176,5304641)):
        assert divisor < 1 << 76 and divisor % 3 == 2
        assert pow(2,h,divisor) == divisor-1 and gcd(divisor,5*prod(bases)) == 1
    for h, chain in ((80,(414721,11)), (208,(928513,464257,232129,167))):
        assert pow(2,h,chain[0]) == chain[0]-1
        assert all(certified_prime(q) and q not in bases and q < 1 << 76 for q in chain)
        assert all((p+1) % q == 0 for p,q in zip(chain,chain[1:]))
        assert chain[-1] % 3 == 2 and chain[-1] != 5

    t = Fraction(1,1 << 76)
    error = Fraction(1,1 << 100)
    assert sum(Fraction(1,p**e) for p,e in zip(bases,min_exponents)) + t*t < error
    lower = 2*(1-4*t)*(1-error)/(1+Fraction(1,1 << 256))
    checks = nodes = 0
    for size in range(len(bases)+1):
        for subset in combinations(bases,size):
            for blocks in SEED_BLOCKS:
                required = tuple(sorted(q for block in blocks for q in block))
                if not set(subset).isdisjoint(required):
                    continue
                possible_bases = (8191 in subset or {65537,131071}.issubset(subset))
                if 8191 not in subset and {524287,(1 << 31)-1}.issubset(subset):
                    possible_bases = False
                if possible_bases and 607 in required:
                    continue
                result = exclude_interval(lower, Fraction(2), subset, required,
                                          bit_cap=320, node_cap=30000, sharpen_tail=True)
                if result is None:
                    raise ArithmeticError(f"Unresolved at {subset}, {required}")
                checks += 1
                nodes += result[0]
    return checks, nodes


if __name__ == "__main__":
    assert modular_chain_certificate((3,7), (7,11,13,17,19)) == [4,18,112,221,0]
    assert modular_chain_certificate((1,9), (7,11,13,17,19,23,29,31,37)) == [
        4,26,87,783,5445,576,576,9099,0]
    assert seed_window_bound(16,13709) == 29
    for all_scales,power in ((False,100),(True,97)):
        windows = normalized_residual_windows(all_scales)
        assert len(windows) == 14 and prod(high/low for low,high in windows)**power < 2
    assert dyadic_root_bound(16,((2147639671,1),)) == 47
    assert three_base_gap_certificate() == (36,12438)
    print("Six-base support intervals and nodes", six_base_gap_certificate(), flush=True)
    mersenne_terminal_certificates()
    for p in (5003, 65537, 13709, 114689, 167772161):
        print(p, capped_shift_exponent_bound(16, ((p,1),), None, node_cap=10000,
                                             bit_cap=48), flush=True)
    print("Terminal bound through 2^24 (primes, intervals, nodes)",
          small_terminal_certificate(), flush=True)
