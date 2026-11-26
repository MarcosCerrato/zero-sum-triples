import sys, time
from xc import *
def p2(k,c,seed=0):
    xs=[x for x in range(-k,k+1) if x!=c]
    items=[('x',x) for x in xs]+[('y',x) for x in xs]+[('d',d) for d in range(-k,k+1) if d!=0]
    opts={}
    for x in xs:
        for d in range(-k,k+1):
            y=x+d
            if d!=0 and -k<=y<=k and y!=c: opts[(x,d)]=[('x',x),('y',y),('d',d)]
    return solve_restarts(items,opts,tries=2000,per=20000,seed=seed,first=100000)
if __name__=="__main__":
    K0,K1=int(sys.argv[1]),int(sys.argv[2])
    for k in range(K0,K1+1):
        t0=time.time(); bad=[]
        for c in range(0,k+1):
            try:
                s=p2(k,c)
                if s is None: bad.append((c,'NONE'))
                else:
                    assert sorted(d for x,d in s)==[d for d in range(-k,k+1) if d]
                    assert sorted(x+d for x,d in s)==sorted(x for x,d in s)==[x for x in range(-k,k+1) if x!=c]
            except TO: bad.append((c,'TO'))
        print(k,"bad:",bad,f"{time.time()-t0:.1f}s",flush=True)
