import random, sys
sys.setrecursionlimit(100000)
class TO(Exception): pass
def solve(items, options, limit=200000, rng=None):
    """items: iterable; options: dict name->list of items. returns list of names or None; raises TO."""
    X={i:set() for i in items}
    for k,v in options.items():
        for e in v: X[e].add(k)
    Y=options; sol=[]; lim=[limit]
    def sel(r):
        cols=[]
        for j in Y[r]:
            for i in X[j]:
                for k in Y[i]:
                    if k!=j: X[k].remove(i)
            cols.append(X.pop(j))
        return cols
    def desel(r,cols):
        for j in reversed(Y[r]):
            X[j]=cols.pop()
            for i in X[j]:
                for k in Y[i]:
                    if k!=j: X[k].add(i)
    def rec():
        if not X: return True
        lim[0]-=1
        if lim[0]<0: raise TO
        best=min(len(v) for v in X.values())
        if best==0: return False
        cand=[c for c in X if len(X[c])==best]
        c=rng.choice(cand) if rng else cand[0]
        rows=list(X[c])
        if rng: rng.shuffle(rows)
        for r in rows:
            sol.append(r); cols=sel(r)
            if rec(): return True
            desel(r,cols); sol.pop()
        return False
    return sol if rec() else None
def solve_restarts(items, options, tries=300, per=30000, seed=0, first=2000000):
    try: return solve(items, options, first if first else per)
    except TO: pass
    rng=random.Random(seed)
    for _ in range(tries):
        try: return solve(items, options, per, rng)
        except TO: continue
    raise TO
def zs(Y):
    """zero-sum triple partition of ±Y"""
    Y=set(Y); items=list(Y)+[-y for y in Y]; opts={}
    for z in Y:
        for x in Y:
            y=z-x
            if x<y and y in Y:
                opts[(z,-x,-y)]=[z,-x,-y]; opts[(-z,x,y)]=[-z,x,y]
    return items,opts
