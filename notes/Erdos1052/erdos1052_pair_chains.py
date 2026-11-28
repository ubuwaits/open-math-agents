"""Low binary digits of two prime chains below (2^(h*l)+1)/(2^h+1).

The direct check uses multiplication. The uniform check uses two additions
and an exact eventual period of the sets of possible digit states.
"""

from functools import lru_cache
from itertools import combinations_with_replacement, product
from math import prod


def digit_rule(primes, forbidden_shifts=None):
    modulus = prod(primes)
    half = (modulus+1)//2
    if forbidden_shifts is None:
        forbidden_shifts = primes

    @lru_cache(None)
    def step(bit, run, residue):
        # At a zero, 1+residue is the current prime and 2+residue its shift.
        if bit == 0:
            if run or any(residue % p == p-1 for p in primes):
                return None
            if any(residue % p == p-2 for p in forbidden_shifts):
                return None
        next_run = (run+1) % 4 if bit else 0
        return next_run, (residue-bit)*half % modulus

    return step


def direct_check(h, horizon, primes):
    """Lift F*p*q=1, one bit at a time, after the first h-1 zero bits."""
    m = h-1
    F = (1 << h)+1
    step = digit_rule(primes)
    # Low pieces p,q, carry (F*p*q-1)/2^i, two unfinished runs and residues.
    states = [(1,1,(F-1) >> m,0,0,0,0)]
    peak, visits = 1, 0
    for i in range(m,horizon):
        new_states = []
        for p,q,carry,l,r,z,w in states:
            for x in (0,1):
                y = (carry+x) % 2
                if p == q and x > y:
                    continue
                left,right = step(x,l,z),step(y,r,w)
                if left is None or right is None:
                    continue
                correction = F*(x*q+y*p+(x*y << i))
                new_states.append((p+(x << i),q+(y << i),(carry+correction)//2,
                                   left[0],right[0],left[1],right[1]))
        states = new_states
        peak,visits = max(peak,len(states)),visits+len(states)
        if not states:
            return i+1,peak,visits
    raise ArithmeticError(f"Surviving pair at h={h} after {horizon} bits")


def uniform_check():
    """Check all h=2^v >= 64 with the same two finite additions."""
    primes = (11,13,29)
    width = 36
    modulus = 1 << width
    step = digit_rule(primes)
    for p in primes:
        assert {pow(2,i,p) for i in range(p-1)} == set(range(1,p))

    def advance(states, place=0):
        new_states = set()
        for a,b,carry,l,r,z,w in states:
            for x in (0,1):
                y = (carry+x) % 2
                left,right = step(x,l,z),step(y,r,w)
                if left is not None and right is not None:
                    new_states.add((a+x*place,b+y*place,(carry+x+y)//2,
                                    left[0],right[0],left[1],right[1]))
        return frozenset(new_states)

    # First add u+v+2, retaining the low 36 bits of u and v.
    states = frozenset([(0,0,2,0,0,0,0)])
    for i in range(width):
        states = advance(states,1 << i)
    # Every step after this point uses exactly the same transition.
    first,history = {},[]
    index = width
    while states not in first:
        first[states] = index
        history.append(states)
        states = advance(states)
        index += 1
    start,period = first[states],index-first[states]

    # m=h-1 evolves by m -> 2*m+1, also modulo the eventual period.
    phases = []
    seen = set()
    m = 63
    while True:
        phase = m if m < start else start+(m-start) % period
        if m >= start:
            if phase in seen:
                break
            seen.add(phase)
        phases.append(phase)
        m = 2*m+1

    # The second addition has the correction uv+2u+2v, modulo 2^36.
    depths = []
    for phase in phases:
        states = frozenset((0,0,(c+a*b+2*a+2*b) % modulus,l,r,z,w)
                           for a,b,c,l,r,z,w in history[phase-width])
        for depth in range(1,width+1):
            states = advance(states)
            if not states:
                depths.append(depth)
                break
        else:
            raise ArithmeticError(f"A pair survived the second addition at phase {phase}")
    return start,period,tuple(zip(phases,depths))


def three_prime_check(h, horizon, primes):
    """Direct three-factor lift, including the allowed initial residues modulo seven."""
    m = h-2
    F = (1 << h)+1
    modulus = prod(primes)
    assert 7 in primes
    for p in primes:
        if p != 7:
            assert p-1 <= m
            assert {pow(2,i,p) for i in range(p-1)} == set(range(1,p))
    # All high vertices avoid all sieving primes. Shifts can also be sieved
    # at globally unavailable primes and at the tokens spent in 19 and 223.
    step = digit_rule(primes,tuple(p for p in primes if p % 3 == 2 or p in (7,13)))
    residues = [z for z in range(0,modulus,modulus//7) if z % 7 in (0,1,2,4)]
    states = {tuple((1,0,z) for z in triple)
              for triple in combinations_with_replacement(residues,3)
              if prod(1+(1 << m)*z for z in triple) % 7 == 1}
    bits = [tuple(row for row in product((0,1),repeat=3) if sum(row) % 2 == parity)
            for parity in (0,1)]
    peak,visits = len(states),0
    for i in range(m,horizon):
        place = 1 << i
        next_states = set()
        for words in states:
            carry = (F*prod(p for p,_,_ in words)-1)//place
            for row in bits[carry % 2]:
                next_words = []
                for (p,run,z),x in zip(words,row):
                    new = step(x,run,z)
                    if new is None:
                        break
                    next_words.append((p+place*x,*new))
                else:
                    next_states.add(tuple(sorted(next_words)))
        states = next_states
        peak,visits = max(peak,len(states)),visits+len(states)
        if not states:
            return i+1,peak,visits
    raise ArithmeticError(f"Surviving triple at h={h} after {horizon} bits")


if __name__ == "__main__":
    small = direct_check(16,48,(11,))
    assert small == (48,8,145)
    start,period,phases = uniform_check()
    assert (start,period,len(phases),max(d for _,d in phases)) == (431,420,15,36)
    print("h=16, bits, peak and visited states", *small)
    print("Uniform start and period", start, period)
    print("Linear phase and additional bits", phases)
    cases = ((16,85,(5,7,11,13)),(64,154,(5,7,11,13,19,29,37)),
             (128,267,(5,7,11,13,19,29,37,53,59)))
    for (h,horizon,primes),expected in zip(cases,((229,3727),(503,16648),(544,27139))):
        assert three_prime_check(h,horizon,primes) == (horizon,*expected)
        print("Three prime factors, h and bits", h,horizon)
