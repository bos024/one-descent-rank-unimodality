"""Actual QA of stationary-three strong-minor closure and renewal inheritance."""
from pathlib import Path
import sys,json,time,hashlib
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import c_minimum

def main():
    rng=Random(20261031659);ct=Counter();sha=hashlib.sha256();start=time.monotonic()
    for _ in range(400):
        u=rng.randint(4,32);r=rng.randint(2*u,2*u+100);alpha=rng.randint(1,3*u+4*r)
        F=arm_prefix(alpha,[2]*u+[3]*r,alpha+2*u+3*r+1)
        D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];ell=D.index(max(D))
        H=[1]
        for n in range(1,ell+2):H.append(sum(H[max(0,n-3):n]))
        R=[0,0]+[H[n]-H[n-1] for n in range(2,len(H))]
        assert F[:r+3]==H[:min(r+3,len(H))] if len(H)>=r+3 else F[:len(H)]==H
        for n in range(3,ell):
            assert D[n]<=R[n]
            if n>=r+3:
                assert D[n]**2-D[n-1]*D[n+1]>=D[n];ct['strong_INTEGER_minor_budgets_after_r_plus3']+=1
            assert D[n]**2*R[n-1]*R[n+1]>=D[n-1]*D[n+1]*R[n]**2
            ct['WHOLE_relative_tribonacci_LC_centres_through_FIRSTmode']+=1
        c_minimum(F,D,4,len(F)-1,ct);ct['ternary_rich_full_C_hosts']+=1
        NF=arm_prefix(alpha,[2]*u+[3]*(r+1),alpha+2*u+3*(r+1)+1)
        ND=[0,0]+[max(0,NF[n]-NF[n-1]) for n in range(2,len(NF))];e=ND.index(max(ND));Rold=max(i for i,x in enumerate(D) if x)
        assert e<=Rold+1 and e<=ell+3
        for n in range(r+6,e):
            assert all(ND[j]==sum(D[j-i] for i in range(1,4)) for j in range(n-1,n+2))
            if n<=ell:
                assert all(D[j]**2-D[j-1]*D[j+1]>=D[j] for j in range(n-3,n))
                ct['positive_THREE_window_full_old_budget_transfers']+=1
            else:
                assert D[n]-D[n-1]<=0 and D[n-3]-D[n-4]>=1
                assert 2*ND[n]-ND[n-1]-ND[n+1]>=1 and ND[n]-ND[n-1]>=1
                ct['strict_INTEGER_mode_transition_concavity_payments']+=1
            assert ND[n]**2-ND[n-1]*ND[n+1]>=ND[n]
        sha.update(json.dumps([alpha,u,r,ell,e,D[r+2:r+6]],separators=(',',':')).encode())
    out=dict(status='EXACT_QA_STATIONARY_THREE_FULL_C_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),
      seconds=time.monotonic()-start,scope='ProposedALL4<=u<=32,r>=2u,alpha>=1FULLCfromCOMPLETEfiniteu/rdiagonal+unboundedstrong-minor3append+H3relativeinheritance. RandomhostsQAONLY;fullu>=33richentranceandgeneralC/A2/originalUIOPEN.')
    (ROOT/'audit_ternary_rich_complete_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
