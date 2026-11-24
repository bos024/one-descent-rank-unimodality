"""Exact QA for the NEW unbounded analytic proof; not a substitute for its induction."""
from pathlib import Path
from fractions import Fraction as Q
from random import Random
from collections import Counter
from math import comb
import json,time,hashlib,sys
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from verify_binary_ternary_A2_original_family import boxes
rho=Q(3,5);b=Q(35,32);c=Q(3,2);q=Q(6125,6144);v=Q(175,192);offset=Q(125,22)
def at(A,n):return A[n] if 0<=n<len(A) else 0
def missing(U):return min([len(U)+2]+[t+len(U)-i for i,t in enumerate(U)])
def scalar(alpha,U):
    f=sum(rho**k for k in range(alpha+1))
    for t in U:f=1+c*(1-rho**t)*f
    return f
def parts(n,h,lo=1):
    if h==1:
        if n>=lo:yield (n,)
        return
    for x in range(lo,n//h+1):
        for rest in parts(n-x,h-1,x):yield (x,)+rest
def main():
    st=time.monotonic();rng=Random(2026110220);ct=Counter();sha=hashlib.sha256()
    assert q**224<=Q(1,2) and 2240*c**18<=b**171 and c<=b**5
    assert 10*101*v**100<=1
    assert 10*(b-Q(24,25))-1-offset/25==Q(97,880)
    for t in range(2,6):assert 0<=c*(1-rho**t)<=b**(t-1)
    for n in range(18,151):
        assert 2240*c**n<=b**(n*(n+1)//2);ct['triangle_penalty_constant_QA']+=1
    for m in range(1501):
        assert m*q**m<=224
        if m>=100:assert 10*(m+1)*v**m<=1
        ct['dyadic_block_and_large_read_power_QA']+=1
    for case in range(300):
        alpha=rng.randrange(0,20);U=[rng.randint(2,18) for _ in range(rng.randrange(0,22))]
        F=arm(alpha,U)[:-2];f=scalar(alpha,U);M=alpha+sum(t-1 for t in U)
        assert f+offset<=10*b**M
        assert sum(x*rho**n for n,x in enumerate(F))==f
        ct['WHOLE_unsorted_positive_and_zero_seed_norm_controls']+=1
    for D in range(2,29):
      for h in range(2,min(D,12)+1):
       for ds in parts(D,h):
        U=[t+1 for t in ds]
        for alpha in [1,2,5]:
            A=arm(alpha,U)[:-2];a=len(A)-1
            for r in range(D//2):
                x=at(A,a-r-1);y=at(A,a-r);z=at(A,a-r+1)
                if y<z or x-2*y+z<=0:continue
                j=a-r
                assert (j+1)*(2*y-z)>=4*x
                ct['ALL_actual_owner_critical_indexed_raw_gaps']+=1
            ct['complete_small_owner_profiles_QA']+=1
    profiles=[]
    for K in [20,21,25,30,40]:
        profiles += [(1,list(range(2,K))),(1,[K-1]*(K-2)),(10,[K-1]*(K+2)),
                     (1,list(range(2,K-1))+[50*K]),(50*K,list(range(2,K)))]
        for t in [2,3,4,5]:
            for g in [t-1,5,20,80,200]:
                profiles.append((1,[t]*max(g,t-1)+list(range(t+1,K))))
    for beta,V in profiles:
        K=missing(V);assert K>=20
        F=arm(beta,V)[:-2];M=beta+sum(t-1 for t in V);B=max([beta]+[t-1 for t in V]);S=min(M//2,M-B)
        for m in range(S+1,len(F)+2):
            d=at(F,m)-at(F,m-1)
            assert m*d<=1<<m,(K,beta,V,m,S,d)
            ct['ALL_actual_signed_slope_reads_OUTSIDE_strict_CI_head']+=1
        if len(F)<300:
            assert F==boxes(beta,V);ct['independent_positive_suffix_box_controls']+=1
        ct['actual_first_missing_twenty_plus_profiles_QA']+=1
        sha.update(repr((beta,V,F,S)).encode())
    for case in range(300):
        N=rng.randint(3,50);B=[1,1]+[rng.randrange(1000) for _ in range(N-1)]
        E=[0,0]+[2*B[n-1]-B[n] for n in range(2,N+1)]
        W=[0]+[E[n]-E[n-1] for n in range(1,N+1)]
        assert 4*sum(Q(W[n],2**n) for n in range(2,N+1))==1-Q(4*(B[N]-B[N-1]),2**N)
        ct['WHOLE_generic_signed_dyadic_prefix_identity_QA']+=1
    out=dict(status='PASS_QA_NEW_UNBOUNDED_FIRST_MISSING_TWENTY_ACTUAL_SLOPE_THINNESS',
      counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='QA ONLY: exact rational constants, whole fold evaluations, complete small owner critical gaps, every outside-head signed slope in listed ACTUAL unbounded-theorem profiles. Does NOT replace written unbounded proof or Lean kernels. GeneralC/A2/originalOPEN.')
    (ROOT/'audit_actual_dyadic_slope_thinness.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
