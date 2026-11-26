"""New route:  Lemma B(m=3k+1, b) for every b NOT divisible by 3, from
   (good parity) p-extended Skolem sequence of order k                       [Baker 1995]
   (bad parity)  4-cycle gadget on 4 end positions + p-extended Langford sequence, defect 3, order k-2  [Linek-Jiang 1998 / Linek-Mor 2004 Thm 7.2]
   then the '3-adic transfer'  (d, x, -s) -> (3d, 3x+1, -3s-1).
"""
import sys, time
from xc import *
def pairs_with_hole(lo, hi, hole, d0, d1, seed=0):
    # partition [lo..hi] minus hole into pairs {a,a+j}, j=d0..d1 (search stands in for the cited theorems)
    pos=[x for x in range(lo,hi+1) if x!=hole]; ps=set(pos)
    assert len(pos)==2*(d1-d0+1)
    items=[('p',x) for x in pos]+[('d',j) for j in range(d0,d1+1)]
    opts={}
    for x in pos:
        for j in range(d0,d1+1):
            if x+j in ps: opts[(x,j)]=[('p',x),('p',x+j),('d',j)]
    s=solve_restarts(items,opts,tries=3000,per=5000,first=30000,seed=seed)
    return s
def sigma_P2(k,p):
    """permutation sigma of [1..2k+1], sigma(p)=p, displacements = ±[1..k] each once. returns (dict, method)"""
    n=2*k+1; good = (p%2==1) if k%4 in (0,1) else (p%2==0)
    sg={p:p}
    if good:
        s=pairs_with_hole(1,n,p,1,k)
        if s is None: return None,'skolem-none'
        for a,j in s: sg[a]=a+j; sg[a+j]=a
        return sg,'Baker'
    if k-2>=5:
        if p<=n-4: u=n-3; lo,hi=1,n-4
        else: u=1; lo,hi=5,n
        s=pairs_with_hole(lo,hi,p,3,k)
        if s is None: return None,'langford-none'
        for a,j in s: sg[a]=a+j; sg[a+j]=a
        sg[u]=u+1; sg[u+1]=u+3; sg[u+3]=u+2; sg[u+2]=u      # displacements +1,+2,-1,-2
        return sg,'gadget+Langford3'
    # tiny k: direct search for a signed sequence
    from p2 import p2
    s=p2(k,p-k-1)
    if s is None: return None,'direct-none'
    for x,d in s: sg[x+k+1]=x+d+k+1
    return sg,'direct'
def lemmaB(k,b):
    # zero-sum triples partitioning +-([3k+1] minus b), b not divisible by 3
    assert b%3
    c=(b-1)//3 if b%3==1 else -(b+1)//3
    p=c+k+1
    sg,how=sigma_P2(k,p)
    if sg is None: return None,how
    n=2*k+1
    assert sorted(sg)==list(range(1,n+1))==sorted(sg.values())
    assert sorted(sg[x]-x for x in sg)==list(range(-k,k+1)) and sg[p]==p
    tr=[]
    for x in sg:
        if x==p: continue
        X=x-k-1; S=sg[x]-k-1
        tr.append((3*(S-X),3*X+1,-3*S-1))
    return tr,how
def check(k,b,tr):
    m=3*k+1
    assert all(sum(t)==0 and len(set(t))==3 for t in tr)
    assert sorted(x for t in tr for x in t)==sorted([x for x in range(1,m+1) if x!=b]+[-x for x in range(1,m+1) if x!=b])
if __name__=="__main__":
    K0,K1=int(sys.argv[1]),int(sys.argv[2]); from collections import Counter
    for k in range(K0,K1+1):
        t0=time.time(); cnt=Counter(); fails=[]
        for b in range(1,3*k+2):
            if b%3==0: continue
            try: tr,how=lemmaB(k,b)
            except TO: tr,how=None,'TO'
            if tr is None: fails.append((b,how)); continue
            check(k,b,tr); cnt[how]+=1
        print(f"k={k} m={3*k+1}: {dict(cnt)} fails={fails} {time.time()-t0:.1f}s",flush=True)
