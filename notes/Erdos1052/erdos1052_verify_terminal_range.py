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


def verify_interval(p, low, high, required, forbidden):
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
                if q==p or q in forbidden or (q not in (3,5) and q%3!=1) or not possible_prime(q):
                    continue
                new_tokens = tuple(x for i,x in enumerate(tokens) if not mask & (1<<i))+(q,)
                new_missing = missing[1:] if missing and missing[0]==q else missing
                if not visit(q,new_tokens,partial*Fraction(q+1,q),new_missing):
                    return False
        return True
    if not visit(1,(p,),Fraction(1),required):
        raise ArithmeticError(f"Unresolved interval at {p}, {required}, {low}, {high}")
    return nodes


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
    result = verify_range()
    assert result == (34750,1081584)
    print("Verified intervals and nodes", *result)
