"""Independent verifier of the terminal-divisor bound through 2^24.

This uses explicit token subsets, prime ranges obtained from each interval,
and a single geometric bound for every possible suffix.
"""

from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import isqrt, prod


def block_intervals():
    partitions = (
        ((3,5,19,607), (7,223), (31,3967)),
        ((3,5,19,607), (7,223), (31,), (8191,)),
        ((3,5,19), (7,223,1783), (31,991)),
    )
    def abundancy(primes):
        return prod((Fraction(q+1,q) for q in primes),start=Fraction(1))
    for blocks in partitions:
        members = set().union(*blocks)
        for size in range(len(blocks)+1):
            for subset in combinations(blocks,size):
                required = tuple(sorted(q for block in subset for q in block))
                forbidden = members.difference(required)
                yield required, forbidden, abundancy(required), 2/abundancy(forbidden)


@lru_cache(maxsize=100000)
def possible_prime(q):
    if q < 2:
        return False
    for divisor in range(2,64):
        if q % divisor == 0:
            return q == divisor
    return all(pow(b,q-1,q)==1 for b in (2,7,11))


def verify_tokens(initial, low, high, required, forbidden):
    """Use the supplied finite stock of odd factors at the start of the search."""
    nodes = 0
    def visit(previous, tokens, partial, missing):
        nonlocal nodes
        nodes += 1
        if partial >= high:
            return True
        if missing:
            ceiling = missing[0]
        elif partial >= low:
            return False
        else:
            ceiling = int((2*len(tokens)+4)*low/(low-partial))+1
        choices = [(1,0)]
        for i,token in enumerate(tokens):
            choices += [(d*token,mask+(1<<i)) for d,mask in choices if 2*d*token<=ceiling+1]
        for odd,mask in choices:
            shift = 2*odd
            while shift <= previous+1:
                shift *= 2
            while shift <= ceiling+1:
                q = shift-1
                shift *= 2
                if q in forbidden or (q not in (3,5) and q%3!=1) or not possible_prime(q):
                    continue
                new_tokens = tuple(x for i,x in enumerate(tokens) if not mask & (1<<i))+(q,)
                new_missing = missing[1:] if missing and missing[0]==q else missing
                if not visit(q,new_tokens,partial*Fraction(q+1,q),new_missing):
                    return False
        return True
    if not visit(1,initial,Fraction(1),required):
        raise ArithmeticError(f"Unresolved interval at {initial}, {required}, {low}, {high}")
    return nodes


def verify_interval(p, low, high, required, forbidden, copies=1):
    return verify_tokens((p,)*copies,low,high,required,set(forbidden) | {p})


def verify_cubefree_residuals(*, mixed=False):
    """Independently enumerate the required windows with at most two copies per base."""
    from itertools import product

    primes = [2**k-1 for k in (13,17,19,31,61)]
    if mixed:
        primes.append(65537)
    windows = tuple(block_intervals())
    error = Fraction(1,2**(75 if mixed else 76))
    checks = nodes = 0
    for counts in product((0,1,2),repeat=len(primes)):
        tokens = tuple(p for p,e in zip(primes,counts) for _ in range(e))
        small = frozenset(tokens)
        powers = tuple(p-1 if p == 65537 else p+1 for p in tokens)
        mass = sum(Fraction(1,v) for v in powers)
        center = Fraction(prod(tokens),prod(powers))
        for h in (16,64):
            y = Fraction(1,2**h)
            if h == 16 and not mixed and mass+error < y:
                continue
            if h == 64 and mixed and not small:
                continue
            for scale in ((1,2) if mixed else (2,)):
                low = scale*center*(1-error)**2
                if h == 16:
                    low *= (1+y)/(1+y**3)
                high = scale*center*(1+y)/(1-error if mixed else 1)
                for on,off,left,right in windows:
                    lower,upper = max(left,low),min(right,high)
                    if lower < upper and small.isdisjoint(on):
                        nodes += verify_tokens(tokens,lower,upper,on,off | small)
                        checks += 1
    return checks,nodes


def verify_mersenne_squares():
    """Check the small residual squares for both permitted ranges of h."""
    from erdos1052_spectrum import exclude_interval

    assert all(((1 << k)-1) % r == 0 for k,r in ((23,47),(29,233),(37,223)))
    results = {}
    cases = [(13,16),(17,16)] + [(k,64) for k in (13,17,19,31)]
    for k,h in cases:
        p = (1 << k)-1
        center = 2*Fraction(p,1 << k)**2
        if h == 16:
            center *= 1+Fraction(1,1 << 16)
            low,high = center/(1+Fraction(1,1 << 48)),center
        else:
            low,high = center,center*(1+Fraction(1,1 << 64))
        counts = []
        for on,off,bottom,top in block_intervals():
            left,right = max(bottom,low),min(top,high)
            if left >= right:
                continue
            nodes = verify_interval(p,left,right,on,off,copies=2)
            other = exclude_interval(left,right,(p,),on,forbidden=off,
                                     multiplicities={p:2},sharpen_tail=True)
            if other is None:
                raise ArithmeticError(f"Unresolved squared residual at k={k}, h={h}")
            counts.append((nodes,other[0]))
        results[k,h] = counts
    return results


def verify_range():
    limit = 1<<24
    prime = bytearray([1])*(limit+1)
    prime[:2] = bytes(2)
    for p in range(2,isqrt(limit)+1):
        if prime[p]:
            prime[p*p::p] = bytes((limit-p*p)//p+1)
    cases = nodes = 0
    for on,off,bottom,top in block_intervals():
        for scale in (65537,1):
            # The group is just below p*65537/2^k in the first range,
            # and just above p/2^k in the second.
            above = Fraction(1) if scale==65537 else 1+Fraction(1,2**64)
            below = 1+Fraction(1,2**80) if scale==65537 else Fraction(1)
            for k in range(12,(limit*scale).bit_length()):
                first = max(4097,int(bottom*2**k/(scale*above)))
                last = min(limit,int(top*2**k*below/scale)+1)
                for p in range(first,last+1):
                    if not prime[p] or (p*scale).bit_length()!=k+1:
                        continue
                    center = Fraction(p*scale,2**k)
                    low,high = max(bottom,center/below),min(top,center*above)
                    if low < high:
                        cases += 1
                        nodes += verify_interval(p,low,high,on,off)
    return cases,nodes


if __name__ == "__main__":
    assert verify_cubefree_residuals() == (1080,198910)
    print("Verified 1080 cubefree Mersenne intervals", flush=True)
    print("Verified mixed residual intervals and nodes", *verify_cubefree_residuals(mixed=True),
          flush=True)
    squares = [row for rows in verify_mersenne_squares().values() for row in rows]
    assert (len(squares),sum(x for x,_ in squares),sum(y for _,y in squares)) == (18,3347,832)
    print("Verified squared residual intervals", len(squares), flush=True)
    result = verify_range()
    assert result == (34750,1081584)
    print("Verified intervals and nodes", *result)
