"""Find a cyclic cover of the tetrahedron with neither a 4-cycle nor an 8-cycle.

For each sheet count the search tries connected ordered shift triples with
nondecreasing representatives. Direct depth-first search returns a witness.
The sharp example is checked separately by the Lean theorem seven_sharp.
"""
from itertools import product
from math import gcd

def adjacency(m, shifts):
    delta = [[0]*4 for _ in range(4)]
    for (u,v),d in zip([(1,2),(2,3),(3,1)],shifts):
        delta[u][v],delta[v][u]=d,-d
    return [[v*m+(x+delta[u][v])%m for v in range(4) if u!=v]
        for u in range(4) for x in range(m)]

def find_cycle(adj,n,m):
    def dfs(path,seen):
        if len(path)==n:
            return path if path[0] in adj[path[-1]] else None
        for v in adj[path[-1]]:
            if v not in seen:
                ans=dfs(path+[v],seen|{v})
                if ans:
                    return ans
        return None
    for u in (0,m,2*m,3*m):
        path=dfs([u],{u})
        if path:
            return path

for m in range(1,30):
    tested=0
    for shifts in product(range(m),repeat=3):
        if not shifts[0]<=shifts[1]<=shifts[2] or gcd(m,*shifts)!=1:
            continue
        tested+=1
        adj=adjacency(m,shifts)
        if not find_cycle(adj,4,m) and not find_cycle(adj,8,m):
            print('witness', m,shifts,find_cycle(adj,16,m))
            raise SystemExit
    print(m,tested)
