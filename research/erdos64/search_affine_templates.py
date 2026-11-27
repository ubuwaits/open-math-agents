"""Search for signed affine cycle templates on the tetrahedron.

Pass a sign mask from 0 to 7. Bit 0 negates coordinates on chord 12, bit 1
on 23 and bit 2 on 31. Optionally write the certificate rows and words as
JSON with --output. The Lean file checks the words and integer relations.
"""
from functools import lru_cache
from itertools import combinations
from collections import Counter, defaultdict
import argparse
import json

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("mask", type=int, choices=range(8))
parser.add_argument("--output", help="Write the certificate as JSON to this path.")
args = parser.parse_args()
mask = args.mask

zero = (0, 0, 0)
def neg(x):
    return tuple(-i for i in x)

def canon(x):
    return max(x, neg(x))

def diff(x,y):
    return tuple(i-j for i,j in zip(x,y))

edges = {(i,j): zero for i in range(4) for j in range(4) if i!=j}
for k,(i,j) in enumerate([(1,2),(2,3),(3,1)]):
    v=tuple(int(k==l) for l in range(3))
    edges[i,j]=v
    s = -1 if mask & (1 << k) else 1
    edges[j,i]=tuple(-s*u for u in v)
def edge_sign(i,j):
    for k,(a,b) in enumerate([(1,2),(2,3),(3,1)]):
        if {i,j} == {a,b} and mask & (1 << k):
            return -1
    return 1

def rowform(rows):
    a=[list(row) for row in rows]
    r=0
    for col in range(3):
        while True:
            nz=[i for i in range(r,len(a)) if a[i][col]]
            if not nz:
                break
            best=min(nz,key=lambda i: abs(a[i][col]))
            a[r],a[best]=a[best],a[r]
            if a[r][col]<0:
                a[r]=[-x for x in a[r]]
            p=a[r][col]
            for i in range(r+1,len(a)):
                q=a[i][col]//p
                a[i]=[x-q*y for x,y in zip(a[i],a[r])]
            if any(v[col] for v in a[r+1:]):
                continue
            for i in range(r):
                q=a[i][col]//p
                a[i]=[x-q*y for x,y in zip(a[i],a[r])]
            r+=1
            break
    return tuple(map(tuple,a[:r]))

@lru_cache(None)
def reduce_vec(b,v):
    for row in b:
        col=next(i for i,x in enumerate(row) if x)
        q=v[col]//row[col]
        if q:
            v=tuple(x-q*y for x,y in zip(v,row))
    return v

def templates(n):
    result={}
    def visit(path,coords):
        u=path[-1]
        for v in range(path[0],4):
            if u==v or (len(path)>1 and path[-2]==v):
                continue
            dest=tuple(edge_sign(u,v)*a+b for a,b in zip(coords[-1], edges[u,v]))
            if len(path)==n:
                if v!=path[0] or u==path[1]:
                    continue
                # Only one base circuit up to rotation and reversal.
                w=tuple(path)
                if any(p[k:]+p[:k]<w for p in [w, w[::-1]] for k in range(n) if p[k]==v):
                    continue
                collision=frozenset(canon(diff(coords[j],coords[i]))
                   for i,j in combinations(range(n),2) if w[i]==w[j])
                if zero not in collision and canon(dest) not in collision:
                    result.setdefault((canon(dest),collision),w)
            elif (v,dest) not in zip(path,coords):
                visit(path+[v],coords+[dest])
    for start in range(4):
        visit([start],[zero])
    return result

groups=defaultdict(list)
for n in (4,8,16):
    ts=templates(n)
    print(n,'templates',len(ts),flush=True)
    for (end,collision),word in ts.items():
        groups[end].append((word,collision))

solved={}
def solve(b):
    if b in solved:
        return
    choices=[]
    for end, entries in groups.items():
        if reduce_vec(b,end)!=zero:
            continue
        for word,collision in entries:
            reduced=frozenset(max(reduce_vec(b,d),reduce_vec(b,neg(d))) for d in collision)
            if zero not in reduced:
                children=frozenset(rowform(b+(d,)) for d in collision)
                choices.append((len(children),len(word),len(collision),word,children))
    if not choices:
        solved[b]=None
        print('STUCK',b,flush=True)
        return
    _,_,_,word,children=min(choices)
    solved[b]=word
    for c in sorted(children):
        solve(c)

solve(())
print('solved', len(solved), Counter(None if w is None else len(w) for w in solved.values()))
print('root',solved[()])
if any(word is None for word in solved.values()):
    raise SystemExit("The template search left an unresolved relation set.")
if args.output:
    with open(args.output, "w", encoding="utf-8") as output:
        json.dump(list(solved.items()), output)
        output.write("\n")
