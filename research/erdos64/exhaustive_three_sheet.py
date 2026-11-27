"""Test whether an arbitrary three-sheeted cover kills all base 16-cycles."""
from itertools import product
from collections import deque

def graph():
    m=7
    w=[[0,0,0,0],[0,0,0,-2],[0,0,0,1],[0,2,-1,0]]
    return [[v*m+(x+w[u][v])%m for v in range(4) if u!=v]
            for u in range(4) for x in range(m)]

def cycles(adj,n):
    paths=[]
    def visit(root,tr,seen):
        if len(tr)==n:
            if root in adj[tr[-1]] and tr[1]<tr[-1]:
                paths.append(tuple(tr))
            return
        for v in adj[tr[-1]]:
            if v>root and not (seen>>v)&1:
                visit(root,tr+[v], seen|(1<<v))
    for root in range(len(adj)):
        visit(root,[root],1<<root)
    return paths

def cotree(adj):
    table={}
    seen={0}
    q=deque([0])
    while q:
        u=q.popleft()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                q.append(v)
                table[min(u,v),max(u,v)]=None
    i=0
    for u,nb in enumerate(adj):
        for v in nb:
            if u<v and (u,v) not in table:
                table[u,v]=i
                i+=1
    return table,i

def constraints(paths, edges):
    oriented=[]
    signs=set()
    for tr in paths:
        row=[]
        for u,v in zip(tr,tr[1:]+tr[:1]):
            e=edges[min(u,v),max(u,v)]
            if e is not None:
                row.append((e,u<v))
        oriented.append(row)
        signs.add(sum(1<<e for e,_ in row))
    return oriented,signs

def forms(walks, mask, rank):
    res=set()
    for row in walks:
        a=[0]*rank
        for e,forward in row:
            s=1-2*((mask>>e)&1)
            if s<0:
                a=[-i for i in a]
            a[e]+=1 if forward else -s
        v=tuple(i%3 for i in a)
        neg=tuple(-i%3 for i in a)
        res.add(min(v,neg))
    return sorted(res,key=lambda v:sum(bool(x) for x in v))

def avoid_all(rows,rank):
    # Left assignments are tried separately; one bit per right assignment.
    k=rank//2
    left=list(product(range(3),repeat=k))
    right=list(product(range(3),repeat=rank-k))
    universe=(1<<len(right))-1
    cache={}
    for v in {row[k:] for row in rows}:
        bins=[0,0,0]
        relevant=[(j,a) for j,a in enumerate(v) if a]
        for i,vec in enumerate(right):
            bins[sum(a*vec[j] for j,a in relevant)%3]|=1<<i
        cache[v]=[universe^x for x in bins]
    tests=[([(j,a) for j,a in enumerate(row[:k]) if a],cache[row[k:]]) for row in rows]
    for vec in left:
        allowed=universe
        for terms,table in tests:
            allowed &= table[-sum(a*vec[j] for j,a in terms)%3]
            if not allowed:
                break
        if allowed:
            i=(allowed&-allowed).bit_length()-1
            ans=vec+right[i]
            assert all(sum(a*b for a,b in zip(ans,row))%3 for row in rows)
            return ans
    return None

if __name__=='__main__':
    adj=graph()
    paths=cycles(adj,16)
    edges,rank=cotree(adj)
    walks,signs=constraints(paths,edges)
    masks=[m for m in range(1<<rank) if all(bin(m&s).count('1')%2==0 for s in signs)]
    print('cycles',len(paths),'rank',rank,'sign possibilities',masks,flush=True)
    assert len(paths) == 441 and rank == 15 and masks == [0, 32767]
    for mask in masks:
        rows=forms(walks,mask,rank)
        witness=avoid_all(rows,rank)
        assert witness is None
        print(f"Sign mask {mask}: {len(rows)} distinct hyperplanes cover all translations.")
