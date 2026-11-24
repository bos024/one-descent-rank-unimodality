"""Exact QA of universal physical-W C and maximal-margin normalized tilts."""
from pathlib import Path
import sys,json,time,hashlib
from fractions import Fraction as Q
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
from audit_arbitrary_Fibonacci_tail_late_C import sign
def qsquare(v):
    v=Q(v);return sign((v.numerator-2*v.denominator,v.denominator))>=0
def model(alpha,u,V,ct):
    W=sum(V);h=W-len(V);F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+1);G=list(accumulate(F))
    D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];A,B=D[W-1:W+1]
    if u>=5 and h>u and len(V)>=2 and B>A>0:
        mu=Q(B,A);assert sign((-B,A))>0
        for k in range(1,W):
            assert qsquare(G[k]-mu*G[k-1]);ct['full_boundary_strong_additive_prefix_reads']+=1
        ct['strict_multifactor_physical_boundaries']+=1
    c_minimum(F,D,W,len(F)-1,ct);ct['actual_hosts']+=1
    return F,G,D
def main():
    rng=Random(20261031473);ct=Counter();sha=hashlib.sha256();start=time.monotonic()
    for L in range(3,95):
        R=rebuild([L],L+1);G=list(accumulate(R));r=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))]
        lam=Q(r[L],r[L-1]);assert 1<=lam<=2
        for k in range(1,L):assert G[k]-lam*G[k-1]>=2-lam
        for a in {Q(1),Q(3,4),Q(9,10)}:
            mu=a*lam
            if mu<=1:continue
            F=[Q(1),Q(1)]
            for n in range(2,L):F.append(F[-1]+a**(n-2)*r[n])
            GT=list(accumulate(F))
            for k in range(1,L):
                K=2*(1-a)+(k-1)*(1-a)**2
                lower=K+(2-lam)*(1+k*(1-a)-K)+(a*a-1)*(1+k*(1-mu))
                assert lower-a*a*(2-mu)==(k-1)*(1-a)*a*a*lam>=0
                assert GT[k]-mu*GT[k-1]>=2-mu;ct['maximal_margin_tilt_FULL_row_reads']+=1
        ct['onefactor_reference_prefix_profiles']+=1
    # Onefactor crossing, protected exception, then arbitrary suffixes with explicit two-edge cap.
    for u in range(5,81,4):
        for L in {u+2,u+5,(3*u)//2,2*u-1}:
            if L<u+2:continue
            for alpha in {1,2,2*u+L}:
                V=[L];old=model(alpha,u,V,ct)
                for step in range(3):
                    t=rng.randint(V[-1],max(V[-1],2*u-1));a=sum(V);b=a+t
                    NF,NG,ND=model(alpha,u,V+[t],ct);A,B=ND[b-1:b+1]
                    if B>A>0:
                        F,G,D=old;mu=Q(B,A);lam0=Q(D[a],D[a-1]);lam1=Q(D[a+1],D[a])
                        cap=max(Q(1),lam0,lam1);assert mu<=cap
                        assert B*F[b-2]<=A*F[b-1]
                        protected=len(V)==1 and V[0]-1-u==1
                        for k in range(1,a):
                            if not protected:assert qsquare(G[k]-cap*G[k-1])
                            assert qsquare(G[k]-mu*G[k-1]);ct['two_edge_OR_protected_old_prefix_margins']+=1
                        for k in range(a,b-1):
                            assert B*F[k-1]<=A*F[k]
                            assert qsquare(G[k]-mu*G[k-1]);ct['LC_extended_old_ordinary_and_cumulative_margins']+=1
                        ct['strict_hereditary_boundary_transfers']+=1
                        if protected:ct['protected_onefactor_exception_transfers']+=1
                    V=V+[t];old=(NF,NG,ND)
                sha.update(json.dumps([alpha,u,L,V,ND[sum(V)-1:sum(V)+1]],separators=(',',':')).encode())
    # Arbitrary first crossings and arbitrary final words cover both initial seed types.
    for _ in range(700):
        V=sorted(rng.choices(range(3,33),k=rng.randint(1,10)));h=sum(t-1 for t in V);u=rng.randint(0,2*h)
        for alpha in {1,u+h+2}:model(alpha,u,V,ct)
    out=dict(status='EXACT_QA_UNIVERSAL_PHYSICAL_BOUNDARY_C_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='ProposedALLactualC fromN>=W,ALLu/h/alpha/V,usingTWO-edge physicalboundary+universalW+1strongG andsharpordinaryLCfromW-1. Protectedr1delta1exceptionkeptseparate;smallurowcone+OLDweight32. FiniteQAONLY;fullN<W C/A2/originalUIOPEN.')
    (ROOT/'audit_universal_physical_boundary_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()

