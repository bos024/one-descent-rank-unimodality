"""Exact root-ring and actual first-defect diagnostics; no sampled universal premise."""
from pathlib import Path
from collections import Counter
from itertools import accumulate
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_renewal_root_primitive_cut import RootField
from audit_minimum_staircase_scaled_dyadic import arm_prefix
def counts(t,N):
    h=[1]
    for n in range(1,N+1):h.append(sum(h[max(0,n-t):n]))
    return h
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();data=[]
    for t in list(range(2,17))+[20,25,32]:
        f=RootField(t);N=120 if t<=16 else 60;l=(1,)*t
        A=[f.power(t-i) for i in range(t)];B=[]
        for i in range(t):
            b=f.zero
            for k in range(1,t-i+1):b=f.add(b,f.power(k))
            B.append(b)
        total=f.zero
        for a in A:assert f.sign(a)>0;total=f.add(total,a)
        assert total==f.one and B[0]==f.one
        for i in range(1,t):assert f.sub(B[i],f.mul(l,B[i-1]))==f.scale(f.one,-1)
        assert f.mul(l,B[-1])==f.one
        for i in range(1,t):assert f.sub(B[i-1],B[i])==A[i-1]
        assert B[-1]==A[-1]
        h=counts(t,N);g=list(accumulate(h));U=[f.one]
        for n in range(1,N+1):
            u=f.zero
            for i in range(min(t,n)):u=f.add(u,f.mul(A[i],U[n-1-i]))
            U.append(u)
        for n in range(N+1):
            assert U[n]==f.sub(f.scale(f.one,g[n]),f.scale(l,g[n-1] if n else 0))
            c=f.sub(f.scale(f.one,h[n]),f.scale(l,h[n-1] if n else 0))
            assert c==f.sub(U[n],U[n-1] if n else f.zero)
            assert f.sign(U[n])>0
            if n:
                assert f.sign(f.sub(f.one,U[n]))>0
                assert f.sign(f.add(f.one,c))>0 and f.sign(f.sub(f.one,c))>0
                ct['EXACT_all_order_positive_unit_margins_and_strict_rounding']+=1
        row=dict(t=t,N=N,h=h,g=g,U=U);data.append(row);sha.update(str(row).encode())
        ct['EXACT_distinct_orders']+=1
    rng=Random(2026110189)
    cases=[(rng.randint(1,100),[2]*rng.randint(0,45)+sorted(rng.randint(3,20) for _ in range(rng.randint(1,14)))) for _ in range(600)]
    cases +=[(a,[2]*u+[t]*r) for t in range(3,9) for a in [1,2,20] for u in [0,1,7,25,50] for r in [1,5,11,17]]
    for alpha,U in cases:
        t=max(U);F=arm_prefix(alpha,U,alpha+sum(U)+1);h=counts(t,len(F)-1)
        a=next(n for n in range(len(F)) if F[n]!=h[n]);assert a>=3 and F[a]<h[a]
        D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D))
        if not all(F[n]**2>=F[n-1]*F[n+1] for n in range(a,L)):continue
        G=list(accumulate(F));best=1
        for n in range(4,L+1):
            k=n-3
            if G[k]*G[best-1]<G[best]*G[k-1]:best=k
            assert G[best]*D[n-1]>=G[best-1]*D[n]
            ct['actual_conditional_C_all_shift_prefix_payments']+=1
        ct['actual_TRUE_ordinary_firstdefect_premise_hosts']+=1
    # Actual ordinary premise need not hold, although complete C still does.
    F=arm_prefix(1,[2]*20+[3]*6,60);n=19
    assert F[n]**2-F[n-1]*F[n+1]==-4**6
    out=dict(status='EXACT_QA_PASS_UNIVERSAL_RENEWAL_ROUNDING_AND_CONDITIONAL_ORDINARY_C_BRIDGE',
      counts=dict(ct),root_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='Universalall-t/all-nprobabilityrenewalproof,threegenericLeanreports. ActualCbridgeCONDITIONALordinaryLCfromFIRSTH_tdefecttoFIRSTDmode;notunconditionalgeneralC/A2/originalUI. Exactroot/actualtestsQAonly.')
    (ROOT/'universal_renewal_rounding_root_data.json').write_text(json.dumps(data)+'\n')
    (ROOT/'audit_universal_renewal_rounding.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
