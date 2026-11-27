"""Enumerate the projected images of a simple octagon in a bipartite double cover.

Even positions have labels 0 to 3. Odd position i either has its own new
label or agrees with one of the two nonadjacent even positions. Its label is
distinct from every other odd label. Canonicalize vertex names within each
degree class, and test each resulting image for a square.
"""
from itertools import permutations, product
from collections import Counter

def canon(edges):
    vertices=sorted({v for e in edges for v in e})
    deg={v:sum(v in edge for edge in edges) for v in vertices}
    groups=[[v for v in vertices if deg[v]==d] for d in sorted(set(deg.values()))]
    best=None
    for perm in product(*(permutations(g) for g in groups)):
        lab={v:i for i,v in enumerate(v for row in perm for v in row)}
        mapped=tuple(sorted(tuple(sorted([lab[i],lab[j]])) for i,j in edges))
        if best is None or mapped<best:best=mapped
    return best
patterns=Counter()
words={}
for odd in product(*[[4+i,(i+2)%4,(i+3)%4] for i in range(4)]):
    if len(set(odd))!=4: continue
    word=[v for i in range(4) for v in [i,odd[i]]]
    edges={tuple(sorted([a,b])) for a,b in zip(word,word[1:]+word[:1])}
    p=canon(edges);patterns[p]+=1; words[p]=word
def has_cycle(edges,n):
    adj={}
    for a,b in edges:adj.setdefault(a,set()).add(b);adj.setdefault(b,set()).add(a)
    def go(path):
        if len(path)==n:return path[0] in adj[path[-1]]
        return any(go(path+[v]) for v in adj[path[-1]] if v>path[0] and v not in path)
    return any(go([v]) for v in adj)
for p,num in sorted(patterns.items(),key=lambda s:(len({v for e in s[0] for v in e}),s[0])):
    print(len({v for e in p for v in e}),len(p),num,has_cycle(p,4),p,words[p])

assert sum(patterns.values()) == 47 and len(patterns) == 8
