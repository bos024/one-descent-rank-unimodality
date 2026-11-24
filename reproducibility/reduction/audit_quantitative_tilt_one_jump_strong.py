"""Exact finite QA of quantitative normalized tilts and unbounded one-jump strong entrances."""
from pathlib import Path
import sys,json,time,hashlib
from fractions import Fraction as Q
from itertools import accumulate
from collections import Counter
from random import Random
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_arbitrary_Fibonacci_tail_late_C import sign
def main():
    rng=Random(20261031344);ct=Counter();start=time.monotonic();sha=hashlib.sha256();wit=None
    fib=[0,1]
    for _ in range(260):fib.append(fib[-1]+fib[-2])
    for L in range(3,181):
        c=fib[L+1]-1
        coefficients=[2*fib[L]]
        if L==3:coefficients+=[0]
        else:
            coefficients+=[2-2*fib[L-1]]
            for k in range(2,L-2):
                coefficients.append(fib[L]*fib[k+2]-c*fib[k+1])
            coefficients.append(fib[L]**2-c*fib[L-1])
            assert sum(fib[j] for j in range(2,L-2))==fib[L-1]-2
            assert 2*fib[L]-3*fib[L-1]==fib[L-4]
            assert coefficients[-1]>=0
        assert len(coefficients)==L-1
        for a in {Q(1),Q(1,2),Q(5,8),Q(2,3),Q(3,4),Q(99,100),Q(rng.randint(1,99),100)}:
            F=[Q(1),Q(1)]
            for n in range(2,L+1):F.append(F[-1]+a**(n-2)*fib[n])
            P=fib[L]*F[L]-a*c*F[L-1]
            assert P==sum(coef*a**k for k,coef in enumerate(coefficients))
            assert P>=4
            mu=a*c/fib[L]
            if mu>1:
                G=list(accumulate(F))
                for k in range(1,L+1):
                    # Rational additive margin >=q²: sign(X-2,1) >=0.
                    res=G[k]-mu*G[k-1]
                    assert sign((res.numerator-2*res.denominator,res.denominator))>=0
                    ct['tilted_reference_additive_G_margin_reads']+=1
            ct['ALL_capacity_normalized_tilt_ordinary_seed_polynomials']+=1
    for u in range(9,101,3):
        for L in sorted({u+2,u+5,u+8,(3*u)//2,2*u-1}):
            if L<u+2:continue
            for alpha in {1,2,L-u,2*u+3}:
                V=[L]
                for level in range(3):
                    W=sum(V);F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+1);G=list(accumulate(F))
                    D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];a,b=D[W:W+2]
                    if b>a>0:
                        for k in range(1,W+1):
                            assert sign((a*G[k]-b*G[k-1]-2*a,a))>=0
                            ct['actual_onejump_and_suffix_additive_margin_reads']+=1
                        for n in range(W,len(F)-1):
                            assert F[n]**2>=F[n-1]*F[n+1];ct['actual_onejump_and_suffix_ordinary_LC_tail_reads']+=1
                        ct['actual_strict_entries']+=1
                        if level and L-u>=6:
                            ct['strict_entries_with_NEW_onefactor_seed']+=1
                            if wit is None:wit=dict(alpha=alpha,u=u,V=V[:],W=W,pair=[a,b],seed_delta=L-1-u)
                    ct['actual_hosts']+=1
                    if level<2:V.append(rng.randint(V[-1],max(V[-1],min(2*u-1,V[-1]+u//4))))
                sha.update(json.dumps([alpha,u,L,V,D[sum(V):sum(V)+2]],separators=(',',':')).encode())
    assert ct['strict_entries_with_NEW_onefactor_seed']>0
    out=dict(status='EXACT_QA_QUANTITATIVE_TILT_AND_ONEJUMP_STRONG_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),new_seed_witness=wit,seconds=time.monotonic()-start)
    (ROOT/'audit_quantitative_tilt_one_jump_strong.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()

