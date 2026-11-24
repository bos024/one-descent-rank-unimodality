"""Exact finite QA of the universal first-crossing strong entrance; all sampled hosts QA only."""
from pathlib import Path
import sys,json,time,hashlib
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
from audit_arbitrary_Fibonacci_tail_late_C import sign
def main():
    rng=Random(20261031423);ct=Counter();sha=hashlib.sha256();start=time.monotonic();profiles=[]
    for u in list(range(5,9))+list(range(9,82,3)):
        for div in (1,2,3):
            h0=max(2,u//div);profiles.append((u,[h0+1]))
        V=[3]*(u//2);profiles.append((u,V))
    for _ in range(180):
        u=rng.randint(5,100);r=rng.randint(1,max(1,u//4));h0=rng.randint(2*r,u);ds=[2]*r
        for j in range(h0-2*r):ds[rng.randrange(r)]+=1
        profiles.append((u,sorted(d+1 for d in ds)))
    witness=None
    for u,V0 in profiles:
        h0=sum(c-1 for c in V0);r0=len(V0);a=sum(V0);L=u+r0+1
        lo=max(V0[-1],u-h0+2);hi=max(lo,2*u-1)
        for t in {lo,(lo+hi)//2,hi}:
            b=a+t;assert b>=L+1
            RR=rebuild(V0,L+1);RG=list(accumulate(RR))
            for alpha in {1,2,3,2*u+h0+3}:
                F=arm_prefix(alpha,[2]*u+V0,alpha+2*u+a+1);G=list(accumulate(F))
                V=V0+[t];NF=arm_prefix(alpha,[2]*u+V,alpha+2*u+b+1);NG=list(accumulate(NF))
                ND=[0,0]+[max(0,NF[n]-NF[n-1]) for n in range(2,len(NF))]
                for n in range(L,len(F)-1):
                    assert F[n]**2>=F[n-1]*F[n+1];ct['old_surplus_ordinary_LC_centres_INCL_u5to15']+=1
                A,B=ND[b:b+2]
                if B>A>0:
                    assert sign((F[a],-F[a-1]))>0 and sign((-F[b],F[b-1]))>0
                    assert B*F[b-1]<A*F[b]
                    assert G[:L+1]==RG[:L+1]
                    assert A*G[L]-B*G[L-1]>A*G[a-1]-B*G[a-2]
                    for k in range(1,b):
                        assert sign((A*G[k]-B*G[k-1]-2*A,A))>=0
                        ct['old_entire_read_additive_margins']+=1
                    assert A*G[b-1]-B*G[b-2]>A*G[a-1]-B*G[a-2]
                    assert A*NF[b]-B*NF[b-1]==(A*G[b-1]-B*G[b-2])-(A*G[a-1]-B*G[a-2])>0
                    for k in range(1,b+1):
                        assert sign((A*NG[k]-B*NG[k-1]-2*A,A))>=0
                        ct['NEW_strong_G_entire_prefix_reads']+=1
                    for n in range(b,len(NF)-1):
                        assert NF[n]**2>=NF[n-1]*NF[n+1];ct['NEW_entire_ordinary_LC_tail']+=1
                    ct['strict_first_crossings']+=1
                    if u<16:ct['strict_first_crossings_u5_to15']+=1
                    hh=sum(c-1 for c in V);rr=len(V)
                    if 13*hh>17*u+4*rr+30 and hh<=3*u-2 and max(V)<=2*u-1:
                        ct['growing_first_crossings_OUTSIDE_ALL_previous_cones']+=1
                        if witness is None:witness=dict(alpha=alpha,u=u,V=V[:],oldh=h0,oldW=a,newW=b,L=L,pair=[A,B])
                c_minimum(NF,ND,b+1,len(NF)-1,ct);ct['actual_crossing_hosts']+=1
                sha.update(json.dumps([alpha,u,V0,t,A,B],separators=(',',':')).encode())
    assert ct['growing_first_crossings_OUTSIDE_ALL_previous_cones']>0 and ct['strict_first_crossings_u5_to15']>0
    out=dict(status='EXACT_QA_UNIVERSAL_FIRST_CROSSING_STRONG_LATE_C_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),new_first_crossing_witness=witness,seconds=time.monotonic()-start,
      scope='CandidateGENERALactualLATEC,N>=W+1,bycompletefirstcrossingusingSURPLUSordinaryLCandREFERENCEGAPDOMINANCE. No densityrecordhypothesis. ORIGINALearlierC/A2/coefficientUIOPEN. FiniteQAONLY.')
    (ROOT/'audit_universal_first_crossing_strong_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()

