"""Finite falsifier of OPEN generic two-seed closure, never a theorem."""
from pathlib import Path
from math import comb
from random import Random
from collections import Counter
import hashlib,json,time
from audit_joint_structure import fastconv


def binary(m):
    F=[1]
    for _ in range(m):
        G=[1]+[0]*(len(F)+1)
        for j,c in enumerate(F):G[j+1]+=c;G[j+2]+=c
        F=G
    return F


def main():
    start=time.monotonic();rng=Random(249);counts=Counter();sha=hashlib.sha256();bad=None
    for trial in range(100000):
        h=rng.randint(2,55);m=h+rng.randint(0,20)
        slopes=sorted([rng.randint(-8,8) for _ in range(h)],reverse=True);ex=[0]
        for v in slopes:ex.append(ex[-1]+v)
        low=min(ex);L=[2**(v-low) for v in ex]
        assert all(L[j]**2>=L[j-1]*L[j+1] for j in range(1,h))
        alpha=rng.choice([1,2,3,m//2+1,m+1,3*m+5]);F=binary(m)
        Cp=fastconv(F,L);B=fastconv([comb(m+1,j) for j in range(m+2)],L)
        size=max(len(Cp),m+alpha+len(B))
        C=[max(0,(Cp[j] if j<len(Cp) else 0)-
            (B[j-m-alpha] if 0<=j-m-alpha<len(B) else 0)) for j in range(size)]
        minors=[C[n]**2-C[n-1]*C[n+1] for n in range(m,len(C)-1)]
        if minors[0]>=0 and minors[1]>=0:
            counts['eligible_two_seed_profiles']+=1
            for j,v in enumerate(minors):
                counts['conditional_LC_minors']+=1
                if v<0:
                    bad=dict(h=h,m=m,alpha=alpha,L=L,n=m+j,
                        triple=C[m+j-1:m+j+2],minor=v,first_seeds=minors[:2]);break
        counts['arbitrary_LC_numerators']+=1
        sha.update(json.dumps([h,m,alpha,L,C],separators=(',',':')).encode())
        if bad:break
    out=dict(status='FINITE_ONLY_GENERIC_TWO_SEED_CLOSURE_DIAGNOSTIC',
        counts=dict(counts),counter=bad,state_sha256=sha.hexdigest(),
        seconds=time.monotonic()-start,
        scope='OPEN generic two-seed closure. All arithmetic exact integer. No universal LC, C, A2 or original UI conclusion; passing finite numerators is not proof.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
