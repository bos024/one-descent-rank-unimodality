"""Exact finite QA, separate from the complete entrance and unbounded proofs."""
from pathlib import Path
from random import Random
import json,time
ROOT=Path(__file__).resolve().parent


def arm_prefix(alpha,U,N):
    F=[int(n<=alpha) for n in range(N+1)]
    for t in U:
        G=[1]+[0]*N;s=0
        for n in range(1,N+1):
            s+=F[n-1]
            if n>t:s-=F[n-t-1]
            G[n]=s
        F=G
    return F


def main():
    start=time.monotonic();counts={};rng=Random(2026102794)
    for k in range(9,101):
        F=arm_prefix(1,list(range(2,k)),2*k-2)
        assert F[-1]>=(k*k+1)*2**(k-3)+1
        d=[max(0,F[i]-F[i-1]) for i in range(k,2*k-1)]
        assert max(d)>=(k+1)*2**(k-3)+1
        counts['staircase_thresholds']=counts.get('staircase_thresholds',0)+1
    F8=arm_prefix(1,list(range(2,8)),28)
    assert max(F8[i]-F8[i-1] for i in range(1,len(F8)))==234
    for case in range(10000):
        alpha=rng.randint(1,100)
        U=sorted(rng.choices(range(2,80),k=rng.randint(3,80)))
        k=2
        for t in U:k=min(k+1,t+1)
        N=2*k+1;F=arm_prefix(alpha,U,N)
        D=[0,0]+[max(0,F[i]-F[i-1]) for i in range(2,N+1)]
        E=[0,0]+[2*F[i-1]-F[i] for i in range(2,N+1)]
        assert next(i for i,x in enumerate(E) if x)==k
        if k>=9:
            assert max(D[k:2*k-1])>=(k+1)*2**(k-3)+1
            counts['actual_peak_prefixes']=counts.get('actual_peak_prefixes',0)+1
        for r in range(2,k-1):
            n=k+r
            if D[n]>D[n-1] or (D[n]==D[n-1] and D[n+1]>D[n]):
                assert E[n]-E[n-1]>=E[k]*2**(r-2)
                counts['actual_scaled_guarded_edges']=counts.get('actual_scaled_guarded_edges',0)+1
        counts['actual_profiles']=counts.get('actual_profiles',0)+1
    for K in range(4,81):
        for alpha in [1,K+1]:
            N=2*K;F=arm_prefix(alpha,[K-2]*(2*K+2)+[K-1],N)
            E=[0,0]+[2*F[i-1]-F[i] for i in range(2,N+1)]
            assert E[K]==2 and not any(E[:K])
            n=2*K-1
            assert E[n]-E[n-1]==2**(K-2)-2
            assert F[n]-F[n-1]>F[n-1]-F[n-2]>0
            counts['actual_scaled_sharpness_profiles']=counts.get('actual_scaled_sharpness_profiles',0)+1
    out=dict(status='PASS_EXACT_MINIMUM_STAIRCASE_AND_SCALED_DYADIC_QA',counts=counts,
        kappa8_peak_height_counter=234,seconds=time.monotonic()-start,
        scope='Finite exact QA only; separate unbounded containment/growth/append proofs and independent complete entrance establish the theorems.')
    (ROOT/'audit_minimum_staircase_scaled_dyadic.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
