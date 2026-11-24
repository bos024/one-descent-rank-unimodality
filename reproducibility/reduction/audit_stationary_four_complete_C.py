"""Exact QA only for all binary/four counts and the enlarged original coefficient family."""
from pathlib import Path
from itertools import accumulate
from collections import Counter
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from verify_ternary_forward_inverse import qa,qm,qs,sub
from audit_binary_ternary_A2_original_family import arm,examine,core_rel
def reference(r,N):
    h=[1,1]
    for _ in range(N-1):h.append(h[-1]+h[-2])
    for _ in range(r):h=[1]+[sum(h[max(0,n-3):n+1]) for n in range(N)]
    return h
def allC(F,ct,key):
    D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];G=list(accumulate(F));best=1
    for N in range(4,len(F)):
        k=N-3
        if G[k]*G[best-1]<G[best]*G[k-1]:best=k
        assert G[best]*D[N-1]>=G[best-1]*D[N]
        ct[key+'_ALL_current_allshift_prefix_payments']+=1;ct[key+'_logical_shift_reads']+=N-3
    return D
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(2026110193)
    for r in range(81):
        R=reference(r,4*r+25);allC(R,ct,'reference')
        if r>=8:
            W=4*r;H=[(R[n]-(R[n-1] if n else 0),-(R[n-1] if n else 0)) for n in range(len(R))]
            for n in range(r+3,W):
                assert qs(sub(qm(H[n],H[n]),qm(H[n-1],H[n+1])))>=0;ct['reference_physical_H_LC_minors']+=1
            for n in range(r+3,W+1):assert R[n]**2>=R[n-1]*R[n+1];ct['reference_ordinary_head_minors']+=1
            assert R[W+1]**2-R[W]*R[W+2]==-5**r
        sha.update(str((r,R)).encode());ct['reference_unbounded_count_QA_hosts']+=1
    cases=[(u,r,a) for r in range(25) for u in range(3*r+6) for a in [1,2,u+r+5]]
    cases +=[(rng.randint(0,160),rng.randint(0,100),rng.randint(1,250)) for _ in range(350)]
    for u,r,alpha in cases:
        F=arm_prefix(alpha,[2]*u+[4]*r,alpha+2*u+4*r+1);D=allC(F,ct,'actual')
        if r>=8:
            A=r+2 if u==0 else r+3
            if u<=3*r:
                for n in range(A,len(F)-1):assert F[n]**2>=F[n-1]*F[n+1];ct['actual_ENTIRE_ordinary_LC_tail_minors']+=1
            else:
                n=4*r+1;assert F[n]**2-F[n-1]*F[n+1]==-5**r;ct['actual_EXACT_negative_five_power_controls']+=1
        sha.update(str((u,r,alpha,F,D)).encode());ct['actual_ALL_binary_four_count_hosts']+=1
    for i in range(420):
        alpha,beta=rng.randint(1,100),rng.randint(1,100)
        U=[2]*rng.randint(0,40)+[4]*rng.randint(0,40)
        if i%3==0:V=[2]*rng.randint(0,40)+[3]*rng.randint(0,40)
        elif i%3==1:V=[2]*rng.randint(0,40)+sorted(rng.randint(3,80) for _ in range(2))
        else:
            r=rng.randint(1,20);V=[2]*rng.randint(0,40)+[3]*r+[rng.randint(6*r,6*r+70)]
        A,B=arm(alpha,U),arm(beta,V);examine(A,B,ct,sha,bool(U and V))
        maximum=max([1]+U+V);core_rel(A,B,maximum+1,ct,sha,'enlarged_A5_with_B4')
    out=dict(status='EXACT_QA_PASS_ALL_BINARY_FOUR_COMPLETE_C_SHARP_ORDINARY_TAIL_AND_ORIGINAL_FAMILY_UNDER_PROOF_AUDIT',
      counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='FiniteQAONLY. Complete352hostordinaryentrance8554minors+92fieldscalarsareseparatecertifiedproofpremises. Analyticfullr/uheredity/crossingcoversALLparameters. GENERALC/A2/originalUIOPEN;within-armMIXED3and4notasserted.')
    (ROOT/'audit_stationary_four_complete_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
