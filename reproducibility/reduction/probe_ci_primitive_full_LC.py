"""Exact QA of a proved CI kernel; no claim of actual-arm LC closure."""
from pathlib import Path
from itertools import product
from random import Random
from collections import Counter
import hashlib,json,time

ROOT=Path(__file__).resolve().parent

def window(a,t):
    out=[];s=0
    for n in range(len(a)+t-1):
        if n<len(a):s+=a[n]
        if 0<=n-t<len(a):s-=a[n-t]
        out.append(s)
    return out

def lc(a):
    return all(a[n]**2>=a[n-1]*a[n+1] for n in range(1,len(a)-1))

def main():
    start=time.monotonic();rng=Random(20261028133);c=Counter();sha=hashlib.sha256()
    for length in range(1,7):
        for a in product(range(1,5),repeat=length):
            if not lc(a):continue
            for D in range(0,2*length+3):
                for T in range(1,7):
                    b=[sum(a[i] for i in range(max(0,n-T+1),min(n,D-n,len(a)-1)+1))
                       for n in range(D+T+1)]
                    assert lc(b),(a,D,T,b)
                    positive=[i for i,x in enumerate(b) if x]
                    assert not positive or positive==list(range(positive[0],positive[-1]+1))
                    c['generic_fusion_instances']+=1
    for case in range(20000):
        caps=[rng.randint(1,50) for _ in range(rng.randint(0,25))]
        if case%3==0:caps=[2]*rng.randint(0,100)+caps
        rng.shuffle(caps);K=[1];g=[1];D=0
        for t in caps:
            prefix=[0]
            for v in g:prefix.append(prefix[-1]+v)
            fusion=[]
            for n in range(D+t):
                l=max(0,n-t+1);r=min(n,D-n,len(g)-1)
                fusion.append(prefix[r+1]-prefix[l] if l<=r else 0)
            K=window(K,t);D+=t-1
            newg=[max(0,K[n]-(K[n-1] if n else 0)) for n in range(len(K))]
            assert fusion==newg,(caps,t)
            assert lc(newg),(caps,newg)
            g=newg
            c['actual_CI_fusion_steps']+=1
            c['LC_minors_including_zero_extensions']+=max(0,len(g)-2)
        m=min(D//2,D-max([t-1 for t in caps],default=0))
        assert [n for n,x in enumerate(g) if x]==list(range(m+1))
        sha.update((str(caps)+':'+str(g)+'\n').encode())
        c['CI_products']+=1
    # Independent exact polynomial identity for the modified-LC obstruction.
    for L in range(5,101):
        F=[1]+[1+n*(n-1)//2 for n in range(1,L+1)]
        for n in range(4,L):
            assert (F[n]-1)**2-F[n-1]*(F[n+1]-1)==-n<0
            c['unbounded_modified_LC_counterfamily_instances']+=1
    out=dict(status='PASS_CI_FULL_POSITIVE_DIFFERENCE_LC_EXACT_QA',counts=dict(c),
        sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Exact finite QA of written discrete-PL fusion proof. No actual-arm sum closure, general C/A2/original UI theorem or novelty claim.')
    (ROOT/'probe_ci_primitive_full_LC.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
