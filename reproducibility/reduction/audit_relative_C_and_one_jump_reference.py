"""Exact diagnostics for the written unbounded inheritance/reference proofs.

The finite checks are QA, not the logical basis of either theorem.
"""
from pathlib import Path
from fractions import Fraction as Q
from random import Random
import json
import time

ROOT=Path(__file__).resolve().parent


def cumulative(d):
    f=[];g=[];s=1;t=0
    for n,x in enumerate(d):
        if n>=2:s+=x
        f.append(s);t+=s;g.append(t)
    return f,g


def ccheck(d,g,counts,key):
    for n in range(3,len(d)):
        if not d[n] or not d[n-1]:continue
        for k in range(n-2):
            assert g[k]*d[n-1] >= (g[k-1] if k else 0)*d[n],(key,n,k)
            counts[key]=counts.get(key,0)+1


def main():
    start=time.monotonic();rng=Random(20261027);counts={}
    M=140
    fib=[0,1]
    for _ in range(M+8):fib.append(sum(fib[-2:]))
    def f(n):return fib[n] if n>=0 else 0
    for L in range(3,91):
        d=[0,0]+[f(n)-f(n-L) for n in range(2,M+1)]
        _,g=cumulative(d)
        c=L-1;C=f(L-1)+f(L+1)-1-(-1)**L
        assert 0<=C<=c*f(L)
        for k in range(M):
            if k<=L:assert g[k]==f(k+4)-k-2
            if k>=L-2:assert g[k]==f(k+4)-f(k-L+4)-c
            if 1<=k<M:
                minor=g[k]**2-g[k-1]*g[k+1]
                assert minor>=0
                if k<=L-1:
                    assert minor==(k-1)*f(k+1)-2*f(k)+1+(-1)**(k+3)
                if k>=L-1:
                    assert minor==(-1)**((k-L)%2)*C+c*d[k+1],(L,k,minor,C,d[k+1])
                counts['reference_LC_minors']=counts.get('reference_LC_minors',0)+1
        ccheck(d,g,counts,'reference_all_shift_C')
        for a in [Q(1,9),Q(1,2),Q(4,5),Q(1)]:
            tilted=[0,0]+[d[n]*a**(n-2) for n in range(2,44)]
            _,gt=cumulative(tilted)
            ccheck(tilted,gt,counts,'one_jump_tilt_C')
        for _ in range(8):
            rho=Q(1);ratio=Q(1);density=[0,0,1]
            for n in range(3,25):
                ratio*=Q(rng.randint(5,10),10)
                rho*=ratio;density.append(d[n]*rho)
            _,gd=cumulative(density)
            ccheck(density,gd,counts,'one_jump_relative_density_C')
    for trial in range(500):
        d=[0,0,1];_,g=cumulative(d)
        for n in range(3,23):
            bound=min(Q(g[k],g[k-1]) for k in range(1,n-2)) if n>=4 else Q(2)
            top=int(d[-1]*bound)
            x=top if rng.randrange(4) else rng.randint(1,max(1,top))
            d.append(x);_,g=cumulative(d)
        ccheck(d,g,counts,'abstract_reference_C')
        for a in [Q(1,5),Q(2,3),Q(1)]:
            dt=[0,0]+[d[n]*a**(n-2) for n in range(2,len(d))]
            _,gt=cumulative(dt)
            ccheck(dt,gt,counts,'abstract_tilt_C')
            for k in range(1,len(d)-2):
                lam=Q(d[k+2],d[k+1]);mu=a*lam
                H=[g[i]-lam*(g[i-1] if i else 0) for i in range(k+1)]
                def K(j):return 1 if j==0 else 2*(1-a)+(j-1)*(1-a)**2
                left=a*a*(gt[k]-mu*gt[k-1])
                right=sum(K(k-i)*a**i*H[i] for i in range(k+1))+(a*a-1)*(1+k*(1-mu))
                assert left==right
                counts['exact_tilt_kernel_identities']=counts.get('exact_tilt_kernel_identities',0)+1
        rho=Q(1);ratio=Q(1);dd=[0,0,1]
        for n in range(3,len(d)):
            ratio*=Q(rng.randint(7,10),10);rho*=ratio;dd.append(rho*d[n])
        _,gd=cumulative(dd);ccheck(dd,gd,counts,'abstract_relative_density_C')
    out=dict(status='PASS_EXACT_QA_RELATIVE_C_AND_ONE_JUMP_REFERENCE',
        scope='FINITE exact rational/integer QA ONLY. Unbounded theorem proofs are in the accompanying TeX; no actual-arm relative-LC implication is asserted.',
        counts=counts,seconds=time.monotonic()-start,counter=None)
    (ROOT/'audit_relative_C_and_one_jump_reference.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
