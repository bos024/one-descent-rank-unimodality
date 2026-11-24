"""Exact finite QA of the sharp W-1 ordinary coefficient LC theorem."""
from pathlib import Path
import sys,json,time
from random import Random
from math import comb
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
def main():
    ct=Counter();bad={};rng=Random(20261031447);start=time.monotonic()
    for _ in range(1400):
        V=sorted(rng.choices(range(3,38),k=rng.randint(1,9)));h=sum(t-1 for t in V);W=sum(V)
        if h<=5:continue
        u=rng.randint(5,h-1)
        for alpha in {1,2,u+h+3}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+1);M=F.index(max(F))
            for n in range(W-1,len(F)-1):
                mi=F[n]**2-F[n-1]*F[n+1]
                if mi<0:bad.setdefault('ordinary_LC_from_W_minus_one',dict(alpha=alpha,u=u,V=V,n=n,W=W,minor=mi))
                ct['W_minus_one_ordinary_tail_centres']+=1
            ct['hosts']+=1
    fib=[0,1]
    for _ in range(200):fib.append(sum(fib[-2:]))
    sharp=[]
    for T in range(4,90):
        for alpha in (1,2,2*T):
            V=[3,T];W=T+3;F=arm_prefix(alpha,[2]*T+V,W+1)
            triple=[2*fib[T+1]-2,2*fib[T+2]-3,2*fib[T+3]-4]
            assert F[T:T+3]==triple
            minor=F[T+1]**2-F[T]*F[T+2]
            assert minor==1-4*fib[T-2]+4*(-1)**(T+1)<0
            if T==5 and alpha==1:sharp.append(dict(alpha=alpha,u=T,V=V,W=W,centre=T+1,triple=triple,minor=minor))
            ct['unbounded_family_sharpness_QA']+=1
    assert not bad
    out=dict(status='EXACT_QA_SHARP_W_MINUS_ONE_ORDINARY_LC_UNDER_AUDIT',counts=dict(ct),counterexamples=bad,sharpness_witness=sharp,seconds=time.monotonic()-start)
    (ROOT/'audit_sharp_previous_ordinary_LC.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()

