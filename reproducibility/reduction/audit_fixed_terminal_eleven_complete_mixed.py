"""QA ONLY for the new complete mixed source bridge and unrestricted FULL-C criterion."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from random import Random
from collections import Counter
import json,time,hashlib,sys
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_joint_structure import fastconv
from audit_first_missing_twelve_original import fast_greedy,fast_core,weighted_D_UI,first_missing
from verify_binary_ternary_A2_original_family import UI
rho=Q(3,5);b=Q(35,32);offset=Q(125,22);v=Q(175,192)
def at(A,n):return A[n] if 0<=n<len(A) else 0
def eval_poly(A):return sum(x*rho**i for i,x in enumerate(A))
def affine_zero(U):
    F=[0]
    for t in U:
        G=[1]+[0]*(len(F)+t-1);value=0
        for n in range(1,len(G)):
            value+=at(F,n-1)-at(F,n-t-1);G[n]=value
        F=G
    return F
def main():
    st=time.monotonic();rng=Random(202611021113);ct=Counter();sha=hashlib.sha256()
    r4=Q(3,2)*(1-rho**4)/b**3
    assert 25*30030*rho**16*r4**2<=b**60
    assert 100*34**5<=2**34 and 100*v**56<=1 and 200*v**67<=1
    for i in range(500):
        assert comb(i+6,6)*rho**i<=3003*rho**8
        ct['seven_interval_point_bound_QA']+=1
    for m in range(34,401):
        assert 100*m**5<=1<<m
        assert sum(comb(m-2,k) for k in range(6))<=m**5
        ct['WHOLE_short_source_count_polynomial_QA']+=1
    profiles=[]
    for K in [13,14,15,16,20]:
        profiles += [(1,list(range(2,K))),(1,[K-1]*(K-2)),
                     (30*K,list(range(2,K))),(1,list(range(2,K-1))+[30*K])]
        for t in [2,3,4,5]:
            for g in [t-1,10,30,60,100]:profiles.append((1,[t]*max(g,t-1)+list(range(t+1,K))))
    for beta,V in profiles:
        K=first_missing(beta,V);assert K>=13 and all(V[-11+i]>=i+2 for i in range(11))
        F=arm(beta,V)[:-2];pre=arm(beta,V[:-1])[:-2];G=arm(beta,V[:-8])[:-2]
        short=affine_zero(V[-8:-1]);P=[1]
        for t in V[-8:-1]:P=fastconv(P,[1]*t)
        H=fastconv(P,G);long=[0]*7+H
        assert pre==[at(short,n)+at(long,n) for n in range(len(pre))]
        M=beta+sum(t-1 for t in V);MG=beta+sum(t-1 for t in V[:-8]);S=min(M//2,M-max([beta]+[t-1 for t in V]))
        assert M-MG>=60
        if len(G)<600:
            assert eval_poly(G)+offset<=10*b**MG*r4**2
            ct['WHOLE_actual_prefix_offset_norm_QA']+=1
        for m in range(S+1,len(F)+2):
            d=at(F,m)-at(F,m-1);assert 20*d<=1<<m
            ct['ALL_actual_constant_density_reads_OUTSIDE_strict_head']+=1
            if M<=2*m:
                assert m>=34 and at(short,m-1)<=m**5
                assert d<=at(short,m-1)+at(H,m-8)
                ct['ALL_bulk_FULL_seven_source_sum_AND_kernel_reads']+=1
            else:ct['ALL_nonbulk_constant_density_reads']+=1
        ct['actual_kappa_thirteen_plus_profiles']+=1
        sha.update(repr((beta,V,F,S)).encode())
    for K in [13,14,15]:
        S=(1+(K-2)*(K-1)//2)//2
        for alpha in range(1,K-5):
          d=K-alpha
          for e in range(d-2):
            for r in range((min(2*d*(d-3),12*d-25)-e-2)//2+1):
              D=2*r+2+e
              for h in range(2,D+1):
                j=alpha+h+r+2+e
                if j-2<=S:continue
                assert e<=2*r+2 and h+r+1<=5*(r+1)
                ct['complete_finite_owner_geometry_QA_ONLY']+=1
    for extra in [False,True]:
        alpha,beta=1,2;U=[4]*3;V=[2]+[4]*3
        for W in [U,V]:
            for _ in range(8):W.append(2*sum(t for t in W if t>=3))
        assert first_missing(alpha,U)==first_missing(beta,V)==13
        if extra:
            if alpha+sum(U)<beta+sum(V):alpha,beta,U,V=beta,alpha,V,U
            U.append(max(U)+1);ct['ONE_extra_arbitrary_legal_heavier_append']+=1
        A=arm(alpha,U)[:-2];B=arm(beta,V)[:-2]
        assert weighted_D_UI(fastconv(A[::-1],B[::-1]))
        M=max(U+V)+1;H,L,R=fast_core(A,B,M)
        actual=fast_greedy([1]*alpha+U+[M]+list(reversed([1]*beta+V)))
        assert actual==H and all(UI(p) for p in [actual,L,R])
        ct['TRUE_greedy_BOTH_eight_dominant_ORIGINAL_ideals']+=1
        ct['TRUE_greedy_ORIGINAL_rank_counts']+=len(actual);ct['BOTH_relative_polynomials']+=2
        ct['actual_FULL_A2_first_missing_beyond_twelve']+=1
        sha.update(repr((alpha,U,beta,V,M,actual,L,R)).encode())
        print(json.dumps(dict(eight_dominants_extra=extra,ranks=len(actual),seconds=time.monotonic()-st)),flush=True)
    out=dict(status='PASS_QA_COMPLETE_MIXED_SOURCE_AND_UNRESTRICTED_FULL_C_ORIGINAL_CRITERION',
      counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='QA ONLY. ALL7sourcecorrectionsretained;ACTUALconstantdensity/head/kernelidentities,lowK13..15owner-rankgeometry,andTRUEgreedyUNAMPLIFIEDoriginalswithBOTH8dominants(kappa13)inclONEextra(kappa14). DoesNOTprovegeneralC/A2/original or replace unbounded written and Lean arguments.')
    (ROOT/'audit_fixed_terminal_eleven_complete_mixed.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
