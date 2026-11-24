"""Exact finite QA of hereditary strong late-C entrance and arbitrary sorted suffixes."""
from pathlib import Path
import sys,json,hashlib,time
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_arbitrary_Fibonacci_tail_late_C import sign
from audit_homogeneous_reference_and_sharp_entrance import c_minimum
from audit_homogeneous_reference_and_sharp_entrance import rebuild
def invariant(alpha,u,V,ct):
    W=sum(V);h=W-len(V);F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+1)
    D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];G=list(accumulate(F))
    A,B=D[W:W+2]
    gr=list(accumulate(rebuild(V,W)))
    for k in range(1,W+1):
        assert sign((gr[k]-2,1-gr[k-1]))>=0
        ct['reference_additive_golden_square_margins']+=1
    if B>A>0:
        assert sign((-B,A))>0
        for k in range(1,W+1):
            assert sign((A*G[k]-B*G[k-1]-2*A,A))>=0
            ct['strong_prefix_additive_golden_square_margins']+=1
        for n in range(W,len(F)-1):
            assert F[n]**2>=F[n-1]*F[n+1]
            ct['ordinary_LC_entire_tail_minors']+=1
        ct['strict_entries']+=1
    c_minimum(F,D,W+1,len(F)-1,ct)
    return F,D,G
def main():
    start=time.monotonic();rng=Random(20261031315);ct=Counter();sha=hashlib.sha256();witness=None
    profiles=[]
    for u in range(20,121,5):
        for cap in range(3,14):
            V=[];h=0
            while h<u+5:V.append(cap);h+=cap-1
            r=len(V)
            if 4*(u+r)+30<13*(h-u) or sum(V)<33:continue
            profiles.append((u,V))
    for _ in range(90):
        u=rng.randint(24,130);V=[];h=0;cap=rng.randint(3,8)
        while h<u+5:
            cap+=rng.randrange(3);V.append(cap);h+=cap-1
        if 4*(u+len(V))+30>=13*(h-u):profiles.append((u,V))
    for u in (33,48,70,96):
        for delta in range(1,5):
            h=u+delta
            profiles.append((u,[h+1]))
            for r in (2,4,10):
                for balanced in (False,True):
                    ds=[2]*r
                    for j in range(h-2*r):ds[j%r if balanced else -1]+=1
                    profiles.append((u,sorted(d+1 for d in ds)))
    for u,seed in profiles:
        delta=sum(t-1 for t in seed)-u
        for alpha in {1,2,3,delta+1}:
            V=seed[:];old=invariant(alpha,u,V,ct);ct['base_seed_hosts']+=1
            for step in range(3):
                W=sum(V);t=rng.randint(V[-1],max(V[-1],min(2*u-1,4*V[-1]+u//4)))
                Vnew=V+[t];F,D,G=invariant(alpha,u,Vnew,ct);A,B=D[W+t:W+t+2]
                oldF,oldD,oldG=old;oa,ob=oldD[W:W+2]
                if B>A>0:
                    assert ob>oa>0
                    assert B*oa<=A*ob
                    assert B*oldF[W+t-1]<=A*oldF[W+t]
                    for k in range(1,W+t):
                        assert sign((A*oldG[k]-B*oldG[k-1]-2*A,A))>=0
                        ct['old_read_additive_margin_at_NEW_window_ratio']+=1
                    ct['strict_entry_hereditary_transfers']+=1
                    h=sum(ti-1 for ti in Vnew);r=len(Vnew)
                    outside=13*h>17*u+4*r+30
                    genuine=outside and h<=3*u-2 and max(Vnew)<=2*u-1 and u<h-9 and sum(Vnew)>32
                    ct['strict_transfers_outside_final_count_cone']+=outside
                    ct['strict_transfers_outside_all_OLD_late_C_families']+=genuine
                    if genuine and witness is None:
                        witness=dict(alpha=alpha,u=u,seed=seed,appended=Vnew[len(seed):],full_V=Vnew,
                            oldW=W,newW=W+t,old_pair=[oa,ob],new_pair=[A,B],h=h,
                            final_count_cone_deficit=13*h-17*u-4*r-30)
                old=(F,D,G);V=Vnew
                ct['actual_append_transfers']+=1
            sha.update(json.dumps([alpha,u,seed,V,D[sum(V):sum(V)+2]],separators=(',',':')).encode())
    assert ct['strict_transfers_outside_all_OLD_late_C_families']>0 and witness
    out=dict(status='EXACT_QA_HEREDITARY_STRONG_LATE_C_UNDER_AUDIT',counts=dict(ct),
      state_sha256=sha.hexdigest(),actual_new_coverage_witness=witness,seconds=time.monotonic()-start,
      scope='Conditional strong-entry invariant and arbitrary sorted suffix extension; no sampled logical premises; finite QA ONLY until formal/proof audit. ALLactual C fromfinalW+1; not allfromfinalW; original/generalC/A2 OPEN.')
    (ROOT/'audit_hereditary_strong_late_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()

